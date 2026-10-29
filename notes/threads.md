# `--threads N` (phase F)

Brief: `notes/briefs/THREADS.md`. Branch `threads`.

## Status

- **Round 1 of the law review is done.** The reviews are `reviews/{claude,gpt,grok}-threads-law.md`
  and the lead's decisions are `reviews/responses-threads-law-1.md`: 13 items, every one decided.
  This file is the revised design for round 2, a short round on the revised statement.
- **No tracked `.bend` file is edited yet.** The draft below is applied to a scratch copy,
  `data/tmp/threads/draft/framebender`.
- **Check on the scratch copy.** `examples.bend` was checked there through `test/bcheck.sh`
  (`--check-only`): 16 TODOs (the 15 imported laws, plus the new `threads`) and no errors.
  - All 27 new examples hold.
  - The new law type-checks, since `examples.bend` imports `MACHINE.bend`.
  - Two false examples, one on `Args.expecting` and one on `Args.threads`, are each refused.

What round 1 changed:
- **Law `threads` covers every option position (item 1).** It holds wherever the parser expects
  an option, written with Grok's `Args.expecting(pre)`. Before, it covered only right after
  `norm`.
- **`Args.threads` is validated (item 2).** It returns `Some` only for a command line that
  `Args.parse` accepts.
- **Comments:**
  - the memory exception (item 3);
  - no driver internals in the law's comment (item 4);
  - why the law holds (item 5);
  - what `Opts.args` records, and what the 128 limit is (items 8 and 9);
  - "every `--threads` must be valid" (GPT 4).
- **Examples:** the 18 asked for (item 6).
- **Unchanged:** the header, the range, the lemma, the usage string. The runtime constructor is
  kept, to be decided by measurement (items 8 to 12).

## The option

- **Syntax.** `--threads N` is a separate word followed by its value, as with `-w N`;
  `--threads=N` is not the option. It may come anywhere the parser expects an option.
  - Every `--threads` given must be valid, and the last one counts, as with `-c` and `-w`.
  - Right after `-f`, `-c` or `-w`, the word `--threads` is that option's value.
  - It is the same name bcftools uses.
- **Range.** N runs from 1 to 128 (`B.Args.max_threads()`). 128 is a chosen limit: the most
  worker threads Bend's runtime runs, and the size of the driver's tables.
  - 0, 129 and up, a word that is not a number, or a missing value are usage errors (exit 2).
  - A number of 2^48 or more stops in the runtime ("bend: a Nat past ...", exit 1). `-w` does the
    same, and law machine already says so. The usage docs will mention it.
- **Default (no `--threads`).** Every command line accepted today runs exactly as today, and its
  output is byte for byte today's, header included:
  - 16 pieces per batch;
  - Bend's runtime picks the CPU count;
  - the driver keeps 16 pieces read ahead and 32 reference reads in flight.

  The usage message itself changes: it gains `[--threads N]`.

## Where N goes

| what | where | with `--threads N` |
|---|---|---|
| pieces judged at once (a batch) | `norm.bend` (`kmax()`, code) | N [16] |
| Bend's worker threads | the runtime, set before `main` | N [CPU count], if kept (below) |
| VCF pieces read ahead | `io64.c` (`IO64_AHEAD`) | N [16] |
| reference reads in flight | `io64.c` (`IO64_FA_MAX`) | N [32] |

- **Memory follows N.** The lead measured about 11 MB per batched piece (608 MB at 16, 782 MB at
  32), plus 3.5 MB per piece read ahead.
  - So Bend's runtime may run out of memory at one N and not at another.
  - That stop is outside law machine (exit 1), and the law's comment, law machine's runtime
    bullet and `docs/LAWS.md` now say so.
- **All of this is code, not law.** The mapping from N to these depths can be tuned later
  without a review (for example a batch of 2N).

**The batch (machine).**
- `kmax()` becomes a field of the parallel machine's state, `W.St{q, bat, k}`.
- `Norm.start` sets it once, from `B.Args.threads(argv)`, with 16 for None.
- Only the test that closes a batch reads it, and no proof uses its value.

**The driver's depths.**
- `main.bend` calls a new effect, `Io.threads(n)`, once, before the first read.
  - n is `B.Args.threads` of the same arguments, or 0 for None.
  - Since item 2, n is always between 0 and 128, whatever the command line, so the driver's
    128-slot tables are safe even if `Io.threads` were called before the usage check.
- `io64.c` keeps the depths `io64_ahead_n` (n, or 16) and `io64_fa_n` (n, or 32). The read-ahead
  ring indexes modulo `io64_ahead_n`.
- `io64.js` gets a no-op.
- The memory agent may edit the same driver files, so I will rebase onto its commit before
  step 2.

**The runtime's threads (item 11: build the constructor, keep it only if it pays).**
- **What it does.** A constructor in `io64.c` (`__attribute__((constructor))`) runs before
  `main`.
  - It reads the command line: from `/proc/self/cmdline` on Linux, from `_NSGetArgv()` on macOS,
    and does nothing elsewhere.
  - It separates the program's words as Bend's `main` does: `+RTS ... -RTS` are the runtime's
    words, and everything after `--RTS` is the program's.
  - It checks the whole grammar of `Args.parse`:
    - the first word is `norm`;
    - `-f`, `-c` and `-w` each take a value; `-c` takes only `e` or `w`, and `-w` takes digits,
      not all zeros;
    - `--threads` takes digits, 1 to 128 once leading zeros are dropped;
    - there is exactly one `-f` and exactly one VCF path;
    - no option is left waiting for its value.
  - Only when the line passes does it prepend `--threads N` to `BENDRTS`, for the last N.
- **It fails safe.** Anything unexpected makes it do nothing: no `/proc`, a read error, an
  unknown word, or a line `Args.parse` would refuse. It therefore only ever sets an N that
  `Args.threads` returns.
- **A user's own setting wins.** A `BENDRTS --threads` or `+RTS --threads M -RTS` from the user
  comes later in the runtime's list, and the runtime takes the last one. So the docs promise no
  exact thread count.
- **Guard.** `build.sh` fails if the generated C no longer reads `getenv("BENDRTS")`.
- **The decision is by measurement.** Step 2 times and measures peak RSS with and without the
  constructor (`--threads N` alone already limits the batch, and the runtime's idle workers
  sleep). It stays only if it shows a gain. It goes to the driver review either way, and the law
  text does not depend on it.

**Not in the header (item 8, kept).** `Opts.args`, which `##framebender_normCommand` prints,
records the arguments that decide the output: all those after `norm` except `--threads` and its
value.

**Not in `Cfg` or `Opts`.**
- The thread count lives only in the parser state (`thr`), and is read by `B.Args.threads`.
- `run`, `run.bend`, `LAWS.bend` and the statements of laws `machine` and `usage` are unchanged.

## The law (revised)

New, in `MACHINE.bend`:

```
# A command line: "norm", then the words pre, then the words post.
def command(pre: List<&2, String>, post: List<&2, String>) -> List<&2, String>:
  "norm" <> List.append(&2, String, pre, post)

# --threads N changes nothing the program writes. Wherever the parser expects
# an option (B.Args.expecting: after "norm", after an option's value, after
# the VCF path), adding --threads N (N from 1 to B.Args.max_threads()) gives
# the same paths and the same report (stdout bytes, messages, exit code) as
# the same command line without it; so two values of N give the same too, at
# any such position. The program may size its work by N. It follows from law
# machine: parse gives the same Cfg with or without --threads N where an option
# is expected, and Opts.args does not record it. Outside this law, as for law
# machine: Bend's runtime may run out of memory at one N and not at another
# (memory grows with N).
law threads:
  for pre: List<&2, String>
  for x: String
  for n: Nat
  for post: List<&2, String>
  for fasta: String
  for vcf: String
  for cs: List<&2, String>
  for he: {B.Args.expecting(pre) == True{} : Bool}
  for hx: {B.Pos.read(x) == Some{n} : Maybe<&2, Nat>}
  for hn: {(Nat.is_le(1n, n) && Nat.is_le(n, B.Args.max_threads())) == True{} : Bool}
  for hf: {P.Fasta.plain(fasta) == True{} : Bool}
  for h: {String.concat(cs) == vcf : String}
  for hb: {E.texts_ok(command(pre, "--threads" <> x <> post), fasta, cs) == True{} : Bool}
  {launch(Norm.start(command(pre, "--threads" <> x <> post)), command(pre, "--threads" <> x <> post), fasta, vcf, cs)
    == launch(Norm.start(command(pre, post)), command(pre, post), fasta, vcf, cs) : Maybe<&2, Launch>}
```

And `B.Args.expecting`, in `types.bend`:

```
# The words pre, read after "norm", leave the parser where an option may come:
# no error so far, and no option waiting for its value.
def Args.expecting(pre: List<&2, String>) -> Bool:
  Args.expecting.of(Args.go(pre, Args.init()))
```

`Args.expecting.of` is `ok` when `pend` is `PNone`, and `False` otherwise.

Notes for round 2:
- **Every position is covered.** `pre` empty is round 1's statement. One N equals the line
  without it, so two values of N agree at every expected-option position:
  - right after `norm`;
  - after a value (`-f r.fa`);
  - after the VCF path (`-f r.fa in.vcf`; example `args_threads_after`).

  Repeated `--threads` options are handled one at a time: remove the last one, then the next.
- **The law is silent where `--threads` is a value.** That is right after `-f`, `-c`, `-w` or
  `--threads`, and also after an error. There, `expecting` is false, which excludes Claude's
  counterexample: `-f --threads 8` names the FASTA `--threads` and the VCF `8`.
  - The examples pin these cases down instead: `args_threads_path`, `args_threads_c`,
    `args_threads_w`, `args_threads_noval`.
- **It holds whether or not `post` parses.** If it does not, both sides are usage errors (`None`).
- **`hb` is stated on the longer line.** `texts_ok` checks each word, so it covers the shorter
  line too.

Why it is true, and the proof plan:
- **The two words change only `thr`.** After `pre` with `expecting`, the step on `--threads` sets
  `pend` to `PThr` and touches nothing else (not `keep`, not `ok`). The step on `x` then sets
  `pend` back to `PNone` and `thr` to `Some{n}`; `ok` stays `True` by `hn`. So the state after
  `pre ++ ["--threads", x]` is the state after `pre`, except for `thr`.
- **The parser lemma.** `Args.go(post, s1)` and `Args.go(post, s2)`, for two states that differ
  only in `thr`, give states that differ only in `thr`, and `Args.done` ignores `thr`. So
  `Args.parse` gives the same result for both lines.
- **Then the cases on `parse`:**
  - `None`: law usage applies to both lines, and `launch` is `None` on both sides.
  - `Some{Cfg{o, ref, vcfpath}}`: law machine applies to both lines, and both sides are
    `Some{Launch{ref, vcfpath, L.run(fasta, vcf, o)}}`.

## The changed parts of the diff, round 1 to round 2

```diff
--- r1/types.bend
+++ r2/types.bend
@@ -710,9 +710,9 @@
 # The options of one run.
 #   strict: True for -c e (the default: a problem stops the run), False for -c w.
 #   w: the sorting window (-w, default 100000, at least 1).
-#   args: the command-line arguments after "norm", recorded in the header,
-#     except --threads and its value: they cannot change the output, and
-#     leaving them out keeps the output the same on every machine.
+#   args: the command-line arguments that decide the output, recorded in the
+#     header: all those after "norm" except --threads and its value (which
+#     only size the program's work), so the output is the same for every N.
 type Opts is Data:
   Opts{strict: Bool, w: Nat, args: List<&2, String>}
 
@@ -725,8 +725,8 @@
 def usage() -> String:
   "usage: framebender norm -f ref.fa [-c e|w] [-w N] [--threads N] in.vcf > out.vcf\n"
 
-# The largest thread count --threads accepts (Bend's runtime runs at most 128
-# worker threads).
+# The largest thread count --threads accepts: a chosen limit, the most worker
+# threads Bend's runtime runs and the size of the driver's tables.
 def Args.max_threads() -> Nat:
   128n
 
@@ -812,8 +812,8 @@
 # The command line after the program name: "norm", then the options -f FASTA
 # (required), -c e or -c w (default e), -w N (N at least 1, default 100000),
 # --threads N (N from 1 to Args.max_threads()) in any order, and one VCF path.
-# None for anything else (a usage error). For -c, -w and --threads the last
-# one given counts.
+# None for anything else (a usage error). For -c, -w and --threads every one
+# given must be valid, and the last one counts.
 def Args.parse(argv: List<&2, String>) -> Maybe<&2, Cfg>:
   match argv:
     case Nil{}:
@@ -821,17 +821,39 @@
     case +cmd <> +rest:
       Args.done.if(String.eq(cmd, "norm"), rest)
 
-def Args.thr_of(st: ArgSt) -> Maybe<&2, Nat>:
+def Args.expecting.of(st: ArgSt) -> Bool:
   match st:
-    case ArgSt{p, s, w, t, r, v, ok, k}:
+    case ArgSt{PNone{}, s, w, t, r, v, ok, k}:
+      ok
+    case _:
+      False{}
+
+# The words pre, read after "norm", leave the parser where an option may come:
+# no error so far, and no option waiting for its value.
+def Args.expecting(pre: List<&2, String>) -> Bool:
+  Args.expecting.of(Args.go(pre, Args.init()))
+
+def Args.thr.done(st: ArgSt) -> Maybe<&2, Nat>:
+  match st:
+    case ArgSt{PNone{}, s, w, t, Some{r}, Some{v}, True{}, k}:
       t
+    case _:
+      None{}
 
-# The thread count a command line asks for (its last --threads N), or None.
-# The program sizes its work by it; law threads (MACHINE.bend) says it never
-# changes the output.
+def Args.threads.if(ok: Bool, rest: List<&2, String>) -> Maybe<&2, Nat>:
+  match ok:
+    case True{}:
+      Args.thr.done(Args.go(rest, Args.init()))
+    case False{}:
+      None{}
+
+# The thread count of a command line Args.parse accepts: Some{n} for its last
+# --threads n (then 1 <= n <= Args.max_threads()), None when it has none. None
+# for every command line Args.parse refuses. The program may size its work by
+# it; law threads (MACHINE.bend) says that changes nothing it writes.
 def Args.threads(argv: List<&2, String>) -> Maybe<&2, Nat>:
   match argv:
     case Nil{}:
       None{}
-    case cmd <> rest:
-      Args.thr_of(Args.go(rest, Args.init()))
+    case +cmd <> +rest:
+      Args.threads.if(String.eq(cmd, "norm"), rest)
--- r1/MACHINE.bend
+++ r2/MACHINE.bend
@@ -184,6 +184,9 @@
 #   spaces, tabs and CRs). The driver reads it through the .fai index (built by
 #   samtools faidx 1.24 from this FASTA file), at 64-bit offsets.
 # - For a FASTA file that is not P.Fasta.plain the law says nothing.
+# - The driver's read-ahead and reference reads in flight, and the runtime's
+#   thread count, follow --threads (B.Args.threads); reading and writing stay
+#   exactly as above.
 # - The driver's own errors, each one line on stderr and exit code 2: a usage
 #   error (law usage; prints B.usage), "error: cannot read <path>", "error:
 #   cannot write", "error: out of memory" (a read's buffer or libdeflate's
@@ -200,7 +203,9 @@
 # - Bend's runtime, also trusted, which can stop a run outside this law, with
 #   one line "bend: ..." on stderr and exit code 1: when the heap is exhausted,
 #   by the machine or by a block the driver allocates for a piece or an answer
-#   ("bend: out of memory: ..."; the driver cannot catch this on a CPU build),
+#   ("bend: out of memory: ..."; the driver cannot catch this on a CPU build;
+#   memory grows with --threads N, so this can happen at one N and not at
+#   another),
 #   and on any number of 2^48 or more, such as a VCF POS that large ("bend: a
 #   Nat past the largest immediate 2^48-1").
 law machine:
@@ -223,23 +228,33 @@
   for ha: {B.Args.parse(argv) == None{} : Maybe<&2, B.Cfg>}
   {Norm.start(argv) == Norm.Usage{} : Norm.Begin}
 
-# The thread count never changes what the program does: --threads N (N from 1
-# to B.Args.max_threads()) right after "norm" gives the same paths and the
-# same report (stdout bytes, messages, exit code) as the same command line
-# without it, so also the same as any other N. The program sizes its work by
-# N (pieces normalized at once; the driver's read-ahead, reference reads in
-# flight and Bend's worker threads), and Opts.args does not record it.
+# A command line: "norm", then the words pre, then the words post.
+def command(pre: List<&2, String>, post: List<&2, String>) -> List<&2, String>:
+  "norm" <> List.append(&2, String, pre, post)
+
+# --threads N changes nothing the program writes. Wherever the parser expects
+# an option (B.Args.expecting: after "norm", after an option's value, after
+# the VCF path), adding --threads N (N from 1 to B.Args.max_threads()) gives
+# the same paths and the same report (stdout bytes, messages, exit code) as
+# the same command line without it; so two values of N give the same too, at
+# any such position. The program may size its work by N. It follows from law
+# machine: parse gives the same Cfg with or without --threads N where an option
+# is expected, and Opts.args does not record it. Outside this law, as for law
+# machine: Bend's runtime may run out of memory at one N and not at another
+# (memory grows with N).
 law threads:
+  for pre: List<&2, String>
   for x: String
   for n: Nat
-  for rest: List<&2, String>
+  for post: List<&2, String>
   for fasta: String
   for vcf: String
   for cs: List<&2, String>
+  for he: {B.Args.expecting(pre) == True{} : Bool}
   for hx: {B.Pos.read(x) == Some{n} : Maybe<&2, Nat>}
   for hn: {(Nat.is_le(1n, n) && Nat.is_le(n, B.Args.max_threads())) == True{} : Bool}
   for hf: {P.Fasta.plain(fasta) == True{} : Bool}
   for h: {String.concat(cs) == vcf : String}
-  for hb: {E.texts_ok("norm" <> "--threads" <> x <> rest, fasta, cs) == True{} : Bool}
-  {launch(Norm.start("norm" <> "--threads" <> x <> rest), "norm" <> "--threads" <> x <> rest, fasta, vcf, cs)
-    == launch(Norm.start("norm" <> rest), "norm" <> rest, fasta, vcf, cs) : Maybe<&2, Launch>}
+  for hb: {E.texts_ok(command(pre, "--threads" <> x <> post), fasta, cs) == True{} : Bool}
+  {launch(Norm.start(command(pre, "--threads" <> x <> post)), command(pre, "--threads" <> x <> post), fasta, vcf, cs)
+    == launch(Norm.start(command(pre, post)), command(pre, post), fasta, vcf, cs) : Maybe<&2, Launch>}
--- r1/examples.bend
+++ r2/examples.bend
@@ -117,6 +117,67 @@
 def args_threads_path() -> {B.Args.parse(["norm", "-f", "--threads", "in.vcf"]) == Some{B.Cfg{B.Opts{True{}, 100000n, ["-f", "--threads", "in.vcf"]}, "--threads", "in.vcf"}} : Maybe<&2, B.Cfg>}:
   {==}
 
+# As the value of -c or -w, "--threads" is a bad value.
+def args_threads_c() -> {B.Args.parse(["norm", "-f", "r.fa", "-c", "--threads", "8", "in.vcf"]) == None{} : Maybe<&2, B.Cfg>}:
+  {==}
+
+def args_threads_w() -> {B.Args.parse(["norm", "-f", "r.fa", "-w", "--threads", "8", "in.vcf"]) == None{} : Maybe<&2, B.Cfg>}:
+  {==}
+
+# A --threads without its number takes the next word as its value.
+def args_threads_noval() -> {B.Args.parse(["norm", "--threads", "-f", "r.fa", "in.vcf"]) == None{} : Maybe<&2, B.Cfg>}:
+  {==}
+
+# Every --threads must be valid, as with -w.
+def args_threads_bad_first() -> {B.Args.parse(["norm", "--threads", "0", "-f", "r.fa", "--threads", "8", "in.vcf"]) == None{} : Maybe<&2, B.Cfg>}:
+  {==}
+
+# A command line refused without --threads is refused with it.
+def args_threads_no_ref() -> {B.Args.parse(["norm", "--threads", "8", "in.vcf"]) == None{} : Maybe<&2, B.Cfg>}:
+  {==}
+
+# After the VCF path, as anywhere an option may come.
+def args_threads_after() -> {B.Args.parse(["norm", "-f", "r.fa", "in.vcf", "--threads", "8"]) == B.Args.parse(["norm", "-f", "r.fa", "in.vcf"]) : Maybe<&2, B.Cfg>}:
+  {==}
+
+# Where an option may come (law threads' B.Args.expecting).
+def expecting_start() -> {B.Args.expecting([]) == True{} : Bool}:
+  {==}
+
+def expecting_after_value() -> {B.Args.expecting(["-f", "r.fa"]) == True{} : Bool}:
+  {==}
+
+def expecting_after_vcf() -> {B.Args.expecting(["-f", "r.fa", "in.vcf"]) == True{} : Bool}:
+  {==}
+
+def expecting_value() -> {B.Args.expecting(["-f"]) == False{} : Bool}:
+  {==}
+
+def expecting_error() -> {B.Args.expecting(["-c", "x"]) == False{} : Bool}:
+  {==}
+
+# Args.threads: Some only for an accepted command line.
+def threads_lead0() -> {B.Args.threads(["norm", "-f", "r.fa", "--threads", "008", "-c", "w", "in.vcf"]) == Some{8n} : Maybe<&2, Nat>}:
+  {==}
+
+def threads_path() -> {B.Args.threads(["norm", "-f", "--threads", "in.vcf"]) == None{} : Maybe<&2, Nat>}:
+  {==}
+
+def threads_zero() -> {B.Args.threads(["norm", "--threads", "0", "-f", "r.fa", "in.vcf"]) == None{} : Maybe<&2, Nat>}:
+  {==}
+
+def threads_big() -> {B.Args.threads(["norm", "--threads", "999", "-f", "r.fa", "in.vcf"]) == None{} : Maybe<&2, Nat>}:
+  {==}
+
+def threads_cmd() -> {B.Args.threads(["x", "--threads", "8", "-f", "r.fa", "in.vcf"]) == None{} : Maybe<&2, Nat>}:
+  {==}
+
+def threads_trailing() -> {B.Args.threads(["norm", "--threads", "4", "-f", "r.fa", "in.vcf", "--threads"]) == None{} : Maybe<&2, Nat>}:
+  {==}
+
+def threads_refused() -> {B.Args.threads(["norm", "--threads", "8", "in.vcf"]) == None{} : Maybe<&2, Nat>}:
+  {==}
+
 # --- Whole runs ------------------------------------------------------------
 
 def fa() -> String:
```

The whole draft against the tree is in `data/tmp/threads/law.diff` (340 lines). Its `types.bend`
part is round 1's plus the changes above.

## What the proofs and examples need (step 2)

- **`examples.bend`:** the 27 cases above, already checked on the scratch copy.
- **`examples_machine.bend`** (outside the gate): `m_threads`, which is `m_pieces` with
  `--threads 1` before the options and with `--threads 3` after the VCF path, expecting the same
  `Launch` as without them.
- **Proofs:**
  1. **The parser's recorded list.** `proof_b_bud_start.bend` (`al_done`, `al_if`) and
     `proof_b_drive_start.bend` (`args_done`, `args_if`) need an invariant over `Args.go`: `keep`
     grows by at most each word, and only by bytes. About 150 lines.
  2. **A new file, `proof_threads.bend`,** with:
     - the parser lemma: the two-word step over `pre`, and agreement over `post` up to `thr`;
     - `all_bytes` of `command(pre, "--threads" <> x <> post)` implies `all_bytes` of
       `command(pre, post)`;
     - law `threads`, from `M.machine`, `M.usage` and the lemma;
     - a lemma for the driver: if `Args.threads(argv) == Some{n}`, then `Args.parse(argv)` is
       `Some` and `1 <= n <= max_threads()`.

     About 300 lines. `PROOF.bend` forwards `M.threads`.
  3. **The batch size in the machine state, `W.St{q, bat, k}`.** This is mechanical: about 14 state
     builders in `norm.bend`, and about 60 proof sites in 9 `proof_e_*` files (the `WPic`
     pictures, the start lemma, the 3 `kmax` sites). About 200 to 300 lines touched.
- **Driver (trusted):**
  - `main.bend` (about 15 lines);
  - `io64.c`: the dynamic depths, and the constructor with its grammar check (about 150 lines);
  - `io64.js`;
  - the `BENDRTS` check in `build.sh`.

  It goes to a driver review.
- **Docs:**
  - README (Run). It opens with "`--threads N` changes only speed and memory, never stdout,
    messages or exit code (except that a larger N needs more memory)". It covers the positions
    and the 2^48 note.
  - `docs/LAWS.md`: law `threads` under "The program", the memory exception under "What the laws
    do not cover", and the driver depths.
  - `docs/DEVELOPMENT.md` and `NOTES.md`.
- **Tests and timing:**
  - `test/par.sh` and `test/same.sh` with `--threads` 1, 2, 3, 7, 16, 32 and 128, at several
    positions, against the default (stdout, stderr and exit code identical), on the normal and
    the small-piece builds;
  - the whole genome with `-c w` and `-c e`;
  - the usage errors;
  - the constructor's grammar check against the `Args.threads` examples;
  - timings and peak RSS for N = 1, 2, 4, 8, 16, 32 and the default, with and without the
    constructor, pinned, under the bench lock.
- **The gate:** `check.sh`, through `test/bcheck.sh`.

Size: about 1 to 2 days of agent work.

## Step 2: implemented and proven (2026-10-29)

Round 2 of the law review (`reviews/*-threads-law-r2.md`, `reviews/responses-threads-law-2.md`):
all three accept. Claude's four minor items, as decided:
1. **`Args.expecting` without `ok`.** It now means only "no option waiting for its value", so the
   law is strictly stronger. The proof does not need the lemma that a false `ok` stays false. The
   parser lemma relates two states that differ only in `thr`, whatever their `ok` is, and
   `Args.done` refuses a false `ok` on both sides alike. So that lemma was not written.
2. **The bound on `Args.threads` is proven** (`proof_f_args.bend`, `threads_ok`): if
   `Args.threads(argv) == Some{n}`, then `Args.parse(argv)` is `Some` and `1 <= n <= 128`.
   `io64.c` also caps the read-ahead depth at 128 (`IO64_AHEAD_MAX`), and the reference-read
   slots are a table of 128 (`IO64_FA_MAX`).
3. **`docs/LAWS.md`:** law `threads` is under "The program", and the memory exception and the
   driver's use of N are under "What the laws do not cover".
4. **"At most"** is the wording for the constructor everywhere (`io64.c`, the docs). Its copy of
   the grammar goes to the driver review.

### Where the batch size lives: a change from the design

The design put the batch size in the parallel machine's state (`W.St{q, bat, k}`). That would have
meant:
- adding a parameter to about 30 functions in `norm.bend`, in the area the memory agent edits
  (`comb.*`, the tasks);
- about 200 changed references in 10,000 lines of `proof_e_wrap*`, `proof_e_bud*` and
  `proof_e_mach*`.

Instead, the driver closes the batches, and no proof changed:
- **The machine already closes a batch at a short piece.** Any piece under `minp()` (256 bytes),
  an empty one included, ends a batch; this is documented in `norm.bend`'s header.
- **Law machine holds for every split of the VCF.** The split includes empty pieces, and
  `E.enc("")` is exactly the driver's `D.Bytes{0, Array.new(U32, 0n, 0)}` (checked by evaluation).
- **The driver sends the empty pieces.** After every N pieces it feeds the machine an empty one
  (16 without `--threads`). `kmax()` becomes 128 (`B.Args.max_threads()`), the machine's own cap.
  Proofs use `kmax()` only as an opaque test.
- **What it costs.**
  - A batch starts only when the sequential machine is quiet, so the first batch takes the
    pieces up to the first empty one (15 at N = 16, as the first piece goes to the sequential
    machine). After that the batches are aligned.
  - If the driver stopped sending empty pieces (a driver bug), batches would grow to 128 pieces:
    more memory, the same output.

  It is driver code, so it goes to the driver review.

The machine's change is then only `kmax()` and two comments (`norm.bend`, +5 -2).

### Files

- **Science and contract (reviewed):**
  - `types.bend`: the parser; `Args.expecting` drops `ok`;
  - `MACHINE.bend`: `command`, law `threads`, the two comment bullets;
  - `examples.bend`: 27 new cases; `expecting_error` now expects True.
- **Proofs:**
  - `proof_f_args.bend` (new, about 650 lines). Lemmas: `kl_go` and `ab_go` (the recorded
    arguments), `un_go` and `done_un` (the thread count is not looked at), `two_words`,
    `parse_thr`, and `threads_ok` (an invariant: `ok` implies the count is in range).
  - `proof_f_threads.bend` (new, about 120 lines): `threads`, from `EM.machine` and `EM.usage`.
  - `proof_b_bud_start.bend` and `proof_b_drive_start.bend`: `al_done`/`al_if` and
    `args_done`/`args_if` rebuilt on `A.kl_go` and `A.ab_go`.
  - `PROOF.bend` forwards `M.threads`.
- **Driver (trusted):**
  - `main.bend`:
    - `Io` carries k (pieces per batch), g (reads started at once) and c (pieces since the last
      empty one);
    - `loop.piece` sends the empty piece;
    - `answers` groups reads by g;
    - `main.t` calls `Io.threads`.
  - `io64.c`:
    - the read-ahead depth `io64_ahead_n` and the `Io.threads` effect;
    - `IO64_FA_MAX` raised to 128;
    - the constructor `io64_rts_threads`, compiled out with `-DFB_NO_RTS_THREADS`.
  - `io64.js`: a no-op `Io.threads`.
- **Not changed:** `build.sh`, which the memory agent rewrites. The `BENDRTS` check is in
  `test/threads.sh` instead. If the runtime stopped reading `BENDRTS`, the constructor would just
  do nothing.
- **Tests:** `test/threads.sh` (new).
- **Docs:** README (Run), `docs/LAWS.md`, `docs/DEVELOPMENT.md`.

### Checks

All checks went through `test/bcheck.sh`, on the final tree:
- `PROOF.bend --check-only`: ALL PROOFS CHECK;
- `PROOF.bend --verdict`: ALL PROOFS CHECK;
- `examples.bend` and `MACHINE.bend`: 16 TODOs each (the imported laws, now including `threads`);
- `main.bend`: 79 defs rely on unsafe or foreign code (62 before: the new and changed driver defs).

Tests (NEW: this branch, built as `build.sh` does; REF: the committed tree, c378c5f; scratch in
`data/tmp/threads/`):
- **`test/same.sh` and `test/par.sh`,** NEW against REF without `--threads` (private copies with
  their own caches, so `data/tmp/rw` and `data/tmp/par` stay untouched):
  - ALL IDENTICAL, 128 and 312 runs, on the normal build and on the 300, 1,000 and 70,001-byte
    builds (`3670016ull` replaced in the generated C, for both NEW and REF).
- **`test/threads.sh`** on the four builds. NEW runs with `--threads N` (N = 1, 2, 3, 7, 16, 32,
  128, rotated over three positions: after `norm`, after `-f FASTA`, after the VCF path). REF runs
  without it. The cases are the edge, batch-boundary, generated, chr22 and scrambled files, under
  `-c e` and `-c w`, with the default `-w` and `-w 1`:
  - ALL IDENTICAL (2,128 runs) on each build;
  - USAGE ERRORS OK: 0, 129, 1000000, x, -1, a missing value, `--threads 0 --threads 8`,
    `-c --threads 8`, `-w --threads 8`;
  - BENDRTS READ.
- **Threads seen on chr22.** `--threads 1`: at most 4. `--threads 3`: at most 7. `--threads 8`:
  at most 10. That is N workers plus the driver's helpers (the read-ahead, and the reference
  readers while the workers wait). Without the constructor: 34 to 36, and REF: 33 (one worker per
  CPU).
- **Whole genome, `-c e`:** REF, and NEW with no option and with N = 1, 7, 32, 128, give the same
  md5 of stdout and stderr, exit 0.
- **Whole genome from the `.vcf.gz`, `-c w`:** REF, and NEW with no option and with N = 4, 32,
  give the same md5.

Timings:
- **Setup.** Whole genome, plain, `-c w`, to a file, pinned to CPUs 0-15, `nice -n 19`, under
  `flock data/tmp/bench.lock`, interleaved, 3 rounds (`data/tmp/threads/bench.sh`).
- **Peak RSS** is from `getrusage(RUSAGE_CHILDREN)`, one Python per run.
- **Identity.** Every run's output had the same md5 (`f70d8639223b`), with exit 0.
- **The `nort` columns** are the build with `-DFB_NO_RTS_THREADS`, the constructor compiled out.
  When pinned, its runtime runs 16 workers, because Bend's CPU count follows the affinity.

| run | wall | peak RSS | nort: wall | nort: peak RSS |
|---|---|---|---|---|
| REF, no option | 2.01-2.35 s | 565-599 MB | | |
| NEW, no option | 1.99-2.02 s | 563-569 MB | | |
| `--threads 1` | 6.96-7.00 s | 109 MB | 7.04-7.62 s | 366-402 MB |
| `--threads 2` | 4.58-4.82 s | 162-194 MB | 4.54-4.78 s | 326-353 MB |
| `--threads 4` | 2.95-3.05 s | 296-330 MB | 3.17-3.25 s | 438-459 MB |
| `--threads 8` | 2.31-2.35 s | 371-375 MB | 2.35-2.37 s | 418-445 MB |
| `--threads 16` | 2.02-2.05 s | 546-552 MB | 2.00-2.02 s | 553-561 MB |
| `--threads 32` | 1.91-1.94 s | 881-883 MB | 1.91-2.00 s | 810-812 MB |

What the numbers say:
- **The default is today's program.** NEW with no option matches REF (REF's 2.35 s is its first
  run).
- **Memory follows N.**
  - It falls from about 565 MB to 109 MB at N = 1 and 162-194 MB at N = 2, at a cost in time:
    7.0 s and 4.6 s.
  - N = 8 costs 15% in time for two thirds of the memory.
  - N = 32 is 5% faster for 880 MB.
- **The constructor stays (item 11).** At small N the runtime's idle workers cost memory: N = 1
  takes 109 MB with the constructor and 366-402 MB without, and N = 4 is 6-7% faster with it.
  From N = 8 up the two builds are the same. At N = 32 the constructor's 32 workers on 16 pinned
  CPUs take 70 MB more than the 16 that the affinity would give. When `--threads` is above the
  CPU count, the user can lower the runtime's threads with `+RTS --threads`.

Open, for the driver review:
- **The constructor's copy of the grammar** in `io64.c` (`io64_threads_of`). The cases to check
  are a lone `-`, an empty word, `+RTS`/`-RTS`/`--RTS`, leading zeros, and huge numbers (capped at
  1000 while read).
- **The empty piece after every k pieces** in `main.bend` (`loop.piece`).
- **`answers` grouping by g.**
- **The read-ahead ring's variable depth.**
