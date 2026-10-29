# Compressed output: `-o` and `-O` (phase H)

Brief: `notes/briefs/COMPRESS.md`. Branch `gz`.

## Status

- **Driver review 8: decisions 1 to 10 fixed** (`reviews/responses-driver8.md`; "Driver review 8"
  at the end). Round 2: Grok and Claude accept; GPT's two items (decision 8) fixed, then decision
  8 amended (a duplicate descriptor instead of the reopen); round 3: Claude accepts, GPT's two
  cases fixed (decisions 11, 12). Not committed.
- **Step 2 is done (2026-10-29): implemented, proven, checked, tested, timed.** See "Step 2" at
  the end; everything above it is the step-1 design as reviewed (the review's decisions, listed
  in step 2, supersede it where they differ). Not committed. Next: the driver review.
- **Step 1 (design and law draft):** reviewed by Claude, GPT and Grok, all accepting (below, as
  it was then).
- **The draft is applied to a scratch copy**, `data/tmp/gz/draft/framebender`, with the diffs
  in `data/tmp/gz/draft/{types,machine,examples}.diff`. They are copied in full below.
  - `examples.bend` was checked there through `test/bcheck.sh` (`--check-only`): 17 TODOs (the
    16 imported laws, plus the new `output`) and no errors.
  - All 27 new examples hold (the draft said 31: a miscount), and the new law type-checks.
  - Two false examples were each refused: one claims `-Oz9 -o out.vcf` is BGZF, the other
    that `-o x.Bcf` is accepted.
- **A scratch prototype measured the cost** (at the end): whole genome, framebender piped into a
  16-thread libdeflate BGZF writer, 3.0 s. `bcftools norm -Oz --threads 16` takes 6.1–6.2 s.
  The prototype's output is byte-identical to `bgzip`'s.

## Summary

- **The options.**
  - `-o FILE`: write the output there (`-o -`: stdout).
  - `-O v|z|z0..z9`, separate or glued (`-Oz`, `-Oz9`): plain or BGZF, with the level on
    htslib's scale.
  - The type follows `-o`'s extension when it names one, as bcftools 1.24 does; otherwise `-O`
    decides. No options means plain output to stdout, as today.
  - BCF (`-O b`, `-O u`, `-o x.bcf`) is a usage error.
- **The header does not record them** (like `--threads`). So `bgzip -dc out.vcf.gz` is byte
  for byte the plain run.
- **The law.** New law `output`, in the style of `law threads`: adding one output option where
  an option is expected changes nothing the program writes. Law machine's comment says how the
  driver writes the output bytes: where, plain or BGZF, and the block layout.
- **The driver** cuts the text into blocks as bgzip 1.24 does. It compresses them on N threads
  with libdeflate (the `--threads` N, 16 by default), writes them in order, then the end-of-file
  block. Compressing the same text therefore gives the same bytes as `framebender ... |
  bgzip -l L`, at every `--threads`. That gives the tests an exact oracle.

## The options

**`-o FILE`.** Write the output to FILE instead of stdout.
- FILE is the next word, whatever it is, as with `-f`. `-o -` means stdout, as in bcftools.
- Refused (a usage error) if FILE ends in `.bcf`, in any case. bcftools writes BCF to such a
  path whatever `-O` says, and framebender writes no BCF.
- Every `-o` given must be valid, and the last one counts, as with `-c`, `-w` and `--threads`.

**`-O T`, also glued as `-OT`.** T is one of:
- `v`: plain VCF;
- `z`: BGZF at the default level;
- `z0` to `z9`: BGZF at that level.

Every `-O` must be valid, and the last one counts.

Refused, each a usage error:
- `b` and `u` (BCF);
- a level past 9 (`-Oz10`);
- a level on `v` (`-Ov5`; bcftools accepts it and ignores the level);
- a bare level (`-O5`, which bcftools accepts);
- any other T;
- `-O` or `-o` with no value.

These were all usage errors before, so no command line accepted today changes meaning. The words
`-o`, `-O` and `-O...` were refused as unknown options until now.

**Which type is written.** This is bcftools 1.24's rule, checked on `bcftools norm` (scratch
runs in `data/tmp/gz`):
1. If `-o`'s path ends, in any case, in `.vcf`, the output is plain. If it ends in `.vcf.gz` or
   `.vcf.bgz`, the output is BGZF. **The extension wins over `-O`.** bcftools 1.24 writes plain
   for `-Oz -o x.vcf` and BGZF for `-Ov -o x.vcf.gz`. I keep that so the name never lies and the
   two tools agree.
2. Otherwise, the last `-O` decides. That covers stdout, `-o -` and any other name, such as
   `out.gz`.
3. Otherwise, the output is plain.

The level is that of the last `-O` if it has one, otherwise the default. `-Oz9 -o x.vcf` is plain
(the level is ignored, as in bcftools); `-Ov -o x.vcf.gz` uses the default level.

**The default level is 6 on htslib's scale (libdeflate 7).** That is what `bcftools -Oz` and
`bgzip` use.
- **Sizes and bytes:** the file is the size users get from bcftools, and the same bytes as
  `framebender | bgzip`.
- **Speed:** the lead holds, at 3.0 s against 6.1–6.2 s (measurements below).
- **The faster choice is one flag away:** `-Oz1` takes 2.4 s for a file 1.7 times larger. It is
  in the README.

**Levels map exactly as htslib 1.24 maps them (verified):**
- 0 is stored blocks (no compression), written by hand as htslib does.
- 1 to 9 become libdeflate levels 1, 2, 3, 5, 6, 7, 8, 10 and 12.
- On chr22, every level from 0 to 9 gives the same bytes as `bgzip -l L`.

**Not taken from bcftools:**
- the long forms `--output` and `--output-type`;
- a glued `-oFILE`;
- `-W` (write an index);
- BCF output, also where bcftools would write VCF by the extension (`-Ou` or `-Ob` with a `.vcf`
  or `.vcf.gz` path: a usage error here);
- a bare level (`-O5`) and a level on `v` (`-Ov5`), which bcftools 1.24 accepts (checked in
  step 2: `-Ov5 -o x.vcf.gz` is BGZF at level 5 there);
- a repeated `-o` or `-O` with an invalid earlier value (bcftools looks only at the last).

The parser has no long forms for `-c` and `-w` either. Any of these can be added later without
changing a command line that is accepted today.

## The header

`-o` and `-O` are **not** recorded in `##framebender_normCommand`, like `--threads`.
- **The text is the same however it is written.** Decompressing `-Oz` output gives byte for
  byte the plain run. That keeps the law a plain equality (the same `Launch`), and it is the
  strongest test.
- **The header stays reproducible.** It would otherwise carry a file name.
- **Cost:** a difference from bcftools, which records its whole command line, `-o` included. The
  header still records everything that decides the records. The README says so.

## The law

A new law `output` in `MACHINE.bend`, stated as `law threads` is.
- Wherever the parser expects an option (`B.Args.expecting(pre)`), adding the words `o` of one
  output option (`B.Args.out_opt(o)`) gives the same launch: the same paths, output bytes,
  messages and exit code.
- One law covers all three forms (`-o P`, `-O T`, `-OT`), because it takes `o` as a list of words.
- Repeated options are dropped one at a time, as with `--threads`.

**How the parser carries these options.** `types.bend` replaces the parser state's `thr: Maybe<Nat>`
with `drv: Drv`, a record of everything that does not decide the text: `Drv{thr, out, typ}`.
- **Why a record.** The parser state keeps its 8 fields, so the roughly 130 lines with
  `ArgSt{...}` patterns in the parser and its proofs stay as they are.
- **The lemmas carry over.** The proof's "differ only in the thread count" (`unthr`) becomes
  "differ only in `drv`".
- **Room for later.** `-W` and BCF later go into `Drv` without touching `ArgSt` again.
- **What the driver reads.** `B.Args.output(argv)` gives a `Sink{file, z, level}` for an
  accepted command line, `None` otherwise. It is the counterpart of `B.Args.threads`.
- **Where the rules live.** `-o`/`-O` semantics, the extension rule and the default level are
  all in the reviewed science layer, pinned by examples. The driver only acts on the `Sink`.

**Law machine's comment changes:**
- it says "output bytes" where it said "stdout bytes";
- a new bullet in "What this law does not cover" says where and how the driver writes those
  bytes: plain, or BGZF with the block layout, the level mapping and the end-of-file block. It
  also says that the file, decompressed, is exactly the output bytes;
- three driver error messages are added.

`LAWS.bend` and `run.bend` do not change.

**What stays trusted, and how it is tested instead:**
- The BGZF writer: cutting the blocks, the gzip member framing, CRC32 and ISIZE, the end-of-file
  block, and the order of the blocks.
- libdeflate's compressor (libdeflate is already trusted for input).
- Opening, emptying and closing the `-o` file, and the check that it is not an input.
- The threads that compress and write.

All of this is tested against independent tools: `bgzip -dc` must give the plain output byte for
byte; the file must be byte-identical to `plain | bgzip -l L`; and `bgzip -t`, `tabix -p vcf`
and `bcftools view` must accept it (test plan below).

**Why the law holds** (the proof plan, as for `threads`):
- From a state where an option is expected, the words of `out_opt(o)` change only `drv`:
  - `-o P`: `ok` is kept, because P is not `.bcf`;
  - `-O T` and `-OT`: `otype(T)` is `Some`.
- So `Args.parse` gives the same result on both lines. Then law `usage` applies to both lines,
  or law `machine` does (`A.same_parse`, already proven in `proof_f_threads.bend`).

## The draft (scratch copy, checked)

The exact edits, as diffs against this branch's tree.

`types.bend`:

```diff
@@ -711,19 +711,22 @@
 #   strict: True for -c e (the default: a problem stops the run), False for -c w.
 #   w: the sorting window (-w, default 1000, at least 1).
 #   args: the command-line arguments that decide the output, recorded in the
-#     header: all those after "norm" except --threads and its value (which
-#     only size the program's work), so the output is the same for every N.
+#     header: all those after "norm" except --threads, -o and -O and their
+#     values (which only size the program's work, or choose how and where the
+#     text is written), so the text is the same for every N, every output
+#     file and every output type.
 type Opts is Data:
   Opts{strict: Bool, w: Nat, args: List<&2, String>}
 
 # A parsed command line: the options, the FASTA path, the VCF path. The thread
-# count (--threads) is not part of it (see Args.threads).
+# count (--threads) and the output options (-o, -O) are not part of it (see
+# Args.threads, Args.output).
 type Cfg is Data:
   Cfg{opts: Opts, ref: String, vcf: String}
 
 # The usage message, printed on a usage error (exit code 2).
 def usage() -> String:
-  "usage: framebender norm -f ref.fa [-c e|w] [-w N] [--threads N] in.vcf > out.vcf\n"
+  "usage: framebender norm -f ref.fa [-c e|w] [-w N] [--threads N] [-o FILE] [-O v|z|z0-9] in.vcf\n"
 
 # The largest thread count --threads accepts: a chosen limit, the most worker
 # threads Bend's runtime runs and the size of the driver's tables.
@@ -737,12 +740,95 @@
   PCheck{}
   PWin{}
   PThr{}
+  POut{}
+  PType{}
 
-# The command line read so far; ok turns False on any error. thr: the thread
-# count; keep: the arguments recorded in the header (all but --threads and its
-# value), in order.
+# An output type, as -O names it: v, plain VCF (z False), or z, VCF in BGZF
+# (z True), with a compression level from 0 to 9 (level, on htslib's scale; None:
+# the default, Args.level).
+type OType is Data:
+  OType{z: Bool, level: Maybe<&2, Nat>}
+
+# What the command line says about how the program works and writes, never
+# about what it writes: the thread count (--threads N), the output path (-o)
+# and the output type (-O); for each, the last one given.
+type Drv is Data:
+  Drv{thr: Maybe<&2, Nat>, out: Maybe<&2, String>, typ: Maybe<&2, OType>}
+
+def Drv.none() -> Drv:
+  Drv{None{}, None{}, None{}}
+
+def Drv.thr(d: Drv) -> Maybe<&2, Nat>:
+  match d:
+    case Drv{t, o, y}:
+      t
+
+def Drv.set_thr(+n: Nat, d: Drv) -> Drv:
+  match d:
+    case Drv{t, o, y}:
+      Drv{Some{n}, o, y}
+
+def Drv.set_out(+x: String, d: Drv) -> Drv:
+  match d:
+    case Drv{t, o, y}:
+      Drv{t, Some{x}, y}
+
+def Drv.set_typ(+x: OType, d: Drv) -> Drv:
+  match d:
+    case Drv{t, o, y}:
+      Drv{t, o, Some{x}}
+
+# Two characters are equal ignoring ASCII case (b in lower case).
+def Args.ceq(a: Char, b: Char) -> Bool:
+  +x = Char.code(a)
+  +y = Char.code(b)
+  U32.is_eq(x, y) || (U32.is_ge(x, 65) && U32.is_le(x, 90) && U32.is_eq(U32.add(x, 32), y))
+
+def Args.eq_ci(a: String, b: String) -> Bool:
+  match a b:
+    case SNil{} SNil{}:
+      True{}
+    case SCon{x, s} SCon{y, t}:
+      Args.ceq(x, y) && Args.eq_ci(s, t)
+    case _ _:
+      False{}
+
+# The word x ends with e (in lower case), in any case: how bcftools 1.24
+# compares a file name's extension.
+def Args.ends_ci(+x: String, +e: String) -> Bool:
+  Nat.is_le(String.length(e), String.length(x)) && Args.eq_ci(String.drop(x, Nat.sub(String.length(x), String.length(e))), e)
+
+# A path that names a BCF file (.bcf): bcftools writes BCF there, whatever -O
+# says. framebender writes no BCF, so -o refuses it.
+def Args.bcf(+x: String) -> Bool:
+  Args.ends_ci(x, ".bcf")
+
+def Args.otype.lvl(ok: Bool, m: Maybe<&2, Nat>) -> Maybe<&2, OType>:
+  match ok m:
+    case True{} Some{+d}:
+      Some{OType{True{}, Some{d}}}
+    case _ _:
+      None{}
+
+# The value of -O: v, z, or z and one digit (the level). BCF (b, u) is not
+# written: a usage error.
+def Args.otype(+x: String) -> Maybe<&2, OType>:
+  Bool.pick(Maybe<&2, OType>, String.eq(x, "v"), Some{OType{False{}, None{}}},
+  Bool.pick(Maybe<&2, OType>, String.eq(x, "z"), Some{OType{True{}, None{}}},
+  Args.otype.lvl(String.starts_with(x, "z") && Nat.is_eq(String.length(x), 2n), Pos.read(String.drop(x, 1n)))))
+
+# The command line read so far; ok turns False on any error. drv: the thread
+# count and the output options; keep: the arguments recorded in the header
+# (all but --threads, -o, -O and their values), in order.
 type ArgSt is Data:
-  ArgSt{pend: Pend, strict: Bool, w: Maybe<&2, Nat>, thr: Maybe<&2, Nat>, ref: Maybe<&2, String>, vcf: Maybe<&2, String>, ok: Bool, keep: List<&2, String>}
+  ArgSt{pend: Pend, strict: Bool, w: Maybe<&2, Nat>, drv: Drv, ref: Maybe<&2, String>, vcf: Maybe<&2, String>, ok: Bool, keep: List<&2, String>}
+
+def Args.typ(m: Maybe<&2, OType>, st: ArgSt) -> ArgSt:
+  match m st:
+    case Some{+y} ArgSt{p, s, w, t, r, v, ok, k}:
+      ArgSt{PNone{}, s, w, Drv.set_typ(y, t), r, v, ok, k}
+    case None{} ArgSt{p, s, w, t, r, v, ok, k}:
+      ArgSt{PNone{}, s, w, t, r, v, False{}, k}
 
 def Args.word(+x: String, st: ArgSt) -> ArgSt:
   match st:
@@ -753,7 +839,10 @@
       Bool.pick(ArgSt, String.eq(x, "-c"), ArgSt{PCheck{}, s, w, t, r, v, ok, kx},
       Bool.pick(ArgSt, String.eq(x, "-w"), ArgSt{PWin{}, s, w, t, r, v, ok, kx},
       Bool.pick(ArgSt, String.eq(x, "--threads"), ArgSt{PThr{}, s, w, t, r, v, ok, k},
-      ArgSt{PNone{}, s, w, t, r, Some{x}, ok && Bool.not(opt) && Maybe.is_none(&2, String, v), kx}))))
+      Bool.pick(ArgSt, String.eq(x, "-o"), ArgSt{POut{}, s, w, t, r, v, ok, k},
+      Bool.pick(ArgSt, String.eq(x, "-O"), ArgSt{PType{}, s, w, t, r, v, ok, k},
+      Bool.pick(ArgSt, String.starts_with(x, "-O"), Args.typ(Args.otype(String.drop(x, 2n)), ArgSt{PType{}, s, w, t, r, v, ok, k}),
+      ArgSt{PNone{}, s, w, t, r, Some{x}, ok && Bool.not(opt) && Maybe.is_none(&2, String, v), kx})))))))
 
 def Args.win(m: Maybe<&2, Nat>, st: ArgSt) -> ArgSt:
   match m st:
@@ -765,12 +854,12 @@
 def Args.thr(m: Maybe<&2, Nat>, st: ArgSt) -> ArgSt:
   match m st:
     case Some{+n} ArgSt{p, s, w, t, r, v, ok, k}:
-      ArgSt{PNone{}, s, w, Some{n}, r, v, ok && Nat.is_le(1n, n) && Nat.is_le(n, Args.max_threads()), k}
+      ArgSt{PNone{}, s, w, Drv.set_thr(n, t), r, v, ok && Nat.is_le(1n, n) && Nat.is_le(n, Args.max_threads()), k}
     case None{} ArgSt{p, s, w, t, r, v, ok, k}:
       ArgSt{PNone{}, s, w, t, r, v, False{}, k}
 
 # The state after one more argument x. Every argument is recorded (keep)
-# except --threads and its value.
+# except --threads, -o and -O (glued -OT too) and their values.
 def Args.step(st: ArgSt, +x: String) -> ArgSt:
   match st:
     case ArgSt{PNone{}, s, w, t, r, v, ok, k}:
@@ -783,6 +872,10 @@
       Args.win(Pos.read(x), ArgSt{PWin{}, s, w, t, r, v, ok, List.append(&2, String, k, [x])})
     case ArgSt{PThr{}, s, w, t, r, v, ok, k}:
       Args.thr(Pos.read(x), ArgSt{PThr{}, s, w, t, r, v, ok, k})
+    case ArgSt{POut{}, s, w, t, r, v, ok, k}:
+      ArgSt{PNone{}, s, w, Drv.set_out(x, t), r, v, ok && Bool.not(Args.bcf(x)), k}
+    case ArgSt{PType{}, s, w, t, r, v, ok, k}:
+      Args.typ(Args.otype(x), ArgSt{PType{}, s, w, t, r, v, ok, k})
 
 def Args.go(xs: List<&2, String>, st: ArgSt) -> ArgSt:
   match xs:
@@ -800,7 +893,7 @@
 
 # The state before the first argument after "norm".
 def Args.init() -> ArgSt:
-  ArgSt{PNone{}, True{}, None{}, None{}, None{}, None{}, True{}, Nil{}}
+  ArgSt{PNone{}, True{}, None{}, Drv.none(), None{}, None{}, True{}, Nil{}}
 
 def Args.done.if(ok: Bool, rest: List<&2, String>) -> Maybe<&2, Cfg>:
   match ok:
@@ -811,9 +904,10 @@
 
 # The command line after the program name: "norm", then the options -f FASTA
 # (required), -c e or -c w (default e), -w N (N at least 1, default 1000),
-# --threads N (N from 1 to Args.max_threads()) in any order, and one VCF path.
-# None for anything else (a usage error). For -c, -w and --threads every one
-# given must be valid, and the last one counts.
+# --threads N (N from 1 to Args.max_threads()), -o PATH (any word not ending
+# in .bcf, in any case), -O T or -OT (T: v, z, z0 to z9) in any order, and one
+# VCF path. None for anything else (a usage error). For -c, -w, --threads, -o
+# and -O every one given must be valid, and the last one counts.
 def Args.parse(argv: List<&2, String>) -> Maybe<&2, Cfg>:
   match argv:
     case Nil{}:
@@ -837,7 +931,7 @@
 def Args.thr.done(st: ArgSt) -> Maybe<&2, Nat>:
   match st:
     case ArgSt{PNone{}, s, w, t, Some{r}, Some{v}, True{}, k}:
-      t
+      Drv.thr(t)
     case _:
       None{}
 
@@ -858,3 +952,109 @@
       None{}
     case +cmd <> +rest:
       Args.threads.if(String.eq(cmd, "norm"), rest)
+
+# ---------------------------------------------------------------------------
+# Output options (they choose how and where the text is written; law output)
+# ---------------------------------------------------------------------------
+
+def Args.out_opt.two(+a: String, +b: String) -> Bool:
+  (String.eq(a, "-o") && Bool.not(Args.bcf(b))) || (String.eq(a, "-O") && Maybe.is_some(&2, OType, Args.otype(b)))
+
+def Args.out_opt.more(+a: String, t: List<&2, String>) -> Bool:
+  match t:
+    case Nil{}:
+      String.starts_with(a, "-O") && Maybe.is_some(&2, OType, Args.otype(String.drop(a, 2n)))
+    case +b <> u:
+      match u:
+        case Nil{}:
+          Args.out_opt.two(a, b)
+        case _:
+          False{}
+
+# One output option, as its words: -o PATH (PATH not ending in .bcf), -O T or
+# the glued -OT (T a type Args.otype accepts).
+def Args.out_opt(o: List<&2, String>) -> Bool:
+  match o:
+    case Nil{}:
+      False{}
+    case +a <> t:
+      Args.out_opt.more(a, t)
+
+# The default compression level of -O z (htslib's and bgzip's default).
+def Args.level() -> Nat:
+  6n
+
+# Where and how the text is written.
+#   file: the path to write, None for stdout (no -o, or -o -);
+#   z: BGZF (True) or plain text; level: the compression level (0 to 9).
+type Sink is Data:
+  Sink{file: Maybe<&2, String>, z: Bool, level: Nat}
+
+def Args.file(o: Maybe<&2, String>) -> Maybe<&2, String>:
+  match o:
+    case None{}:
+      None{}
+    case Some{+p}:
+      Bool.pick(Maybe<&2, String>, String.eq(p, "-"), None{}, Some{p})
+
+# The type a path's extension names, as bcftools 1.24 reads it: .vcf plain,
+# .vcf.gz and .vcf.bgz BGZF (in any case); None for any other path.
+def Args.ext(+p: String) -> Maybe<&2, Bool>:
+  Bool.pick(Maybe<&2, Bool>, Args.ends_ci(p, ".vcf"), Some{False{}},
+  Bool.pick(Maybe<&2, Bool>, Args.ends_ci(p, ".vcf.gz") || Args.ends_ci(p, ".vcf.bgz"), Some{True{}}, None{}))
+
+def Args.ext.of(o: Maybe<&2, String>) -> Maybe<&2, Bool>:
+  match o:
+    case None{}:
+      None{}
+    case Some{+p}:
+      Args.ext(p)
+
+def Args.z.of(e: Maybe<&2, Bool>, y: Maybe<&2, OType>) -> Bool:
+  match e y:
+    case Some{b} _:
+      b
+    case None{} Some{OType{z, l}}:
+      z
+    case None{} None{}:
+      False{}
+
+def Args.level.of(y: Maybe<&2, OType>) -> Nat:
+  match y:
+    case Some{OType{z, Some{l}}}:
+      l
+    case _:
+      Args.level()
+
+# The output: to the -o path (stdout without one, or for -o -); BGZF or plain
+# by the path's extension if it names one (as bcftools 1.24, whatever -O
+# says), else by the last -O (plain without one); the level of the last -O,
+# else Args.level().
+def Args.sink(d: Drv) -> Sink:
+  match d:
+    case Drv{t, +o, +y}:
+      Sink{Args.file(o), Args.z.of(Args.ext.of(o), y), Args.level.of(y)}
+
+def Args.sink.done(st: ArgSt) -> Maybe<&2, Sink>:
+  match st:
+    case ArgSt{PNone{}, s, w, t, Some{r}, Some{v}, True{}, k}:
+      Some{Args.sink(t)}
+    case _:
+      None{}
+
+def Args.output.if(ok: Bool, rest: List<&2, String>) -> Maybe<&2, Sink>:
+  match ok:
+    case True{}:
+      Args.sink.done(Args.go(rest, Args.init()))
+    case False{}:
+      None{}
+
+# The output of a command line Args.parse accepts; None for every command
+# line it refuses. The driver writes the text there; law output
+# (MACHINE.bend) says the output options change nothing in the text.
+def Args.output(argv: List<&2, String>) -> Maybe<&2, Sink>:
+  match argv:
+    case Nil{}:
+      None{}
+    case +cmd <> +rest:
+      Args.output.if(String.eq(cmd, "norm"), rest)
```

`MACHINE.bend`:

```diff
@@ -164,8 +164,8 @@
 # The program: started with a command line B.Args.parse accepts, it opens the
 # FASTA and VCF files it names and, for a FASTA file whose sequence lines hold
 # no spaces or tabs (P.Fasta.plain), however the VCF file is cut into pieces,
-# given truthful reference reads, writes exactly what run says (stdout bytes,
-# stderr messages, exit code), within bound steps and bound reads.
+# given truthful reference reads, writes exactly what run says (the output
+# bytes, stderr messages, exit code), within bound steps and bound reads.
 #
 # What this law does not cover (the trusted driver, main.bend, with its effects
 # in io64.c):
@@ -175,8 +175,17 @@
 #   first two bytes are 1f 8b and that does not start with a BGZF block header
 #   is refused), packing each VCF piece and each reference answer as exactly E.enc of its text (bytes four
 #   to a word, little-endian, zero-padded, in the smallest block), and writing
-#   every stdout byte (the bytes of each output buffer, D.view) and message
+#   every output byte (the bytes of each output buffer, D.view) and message
 #   (B.Note.render) exactly, then exiting with the code.
+# - Where and how the output bytes are written, as B.Args.output(argv) says
+#   (law output): to stdout, or to the file it names (created with mode 0666
+#   less the umask, or emptied first if it is a regular file); as they are, or
+#   in BGZF: cut into blocks as bgzip 1.24 cuts text (each block a whole
+#   number of lines when they fit 65280 bytes, the header's lines apart from
+#   the records), each block a gzip member with the BC extra field, deflated
+#   by libdeflate at the level (htslib's mapping), then the 28-byte empty
+#   end-of-file block, written once the machine finishes, whatever its code.
+#   Decompressed, the file is exactly the output bytes.
 # - Answering each reference read Req{chrom, a, b} of an Ask, in order, with
 #   exactly truth(B.Fasta.parse(fasta), chrom, a, b): Unknown when the .fai has
 #   no such contig, else Known with the contig's length String.length(Contig.raw)
@@ -189,10 +198,16 @@
 #   exactly as above.
 # - The driver's own errors, each one line on stderr and exit code 2: a usage
 #   error (law usage; prints B.usage), "error: cannot read <path>", "error:
-#   cannot write", "error: out of memory" (libdeflate's decompressor),
+#   cannot write" (stdout or stderr), "error: cannot write <path>" (the -o
+#   file: it cannot be opened, written or closed), "error: output is an input
+#   <path>" (the -o file is the VCF, the FASTA or its .fai: refused before
+#   anything is written to it), "error: out of memory" (libdeflate's
+#   decompressor or compressor),
 #   "error: unsupported gzip <path> (not BGZF; ...)", "error:
 #   bad BGZF <path>" (also a BGZF VCF without the end-of-file block, as one cut
-#   at a block boundary), "error: no BGZF in this build <path>", "error: bad
+#   at a block boundary), "error: no BGZF in this build <path>" (a BGZF VCF,
+#   or BGZF output to the -o file <path>, "-" for stdout, in a build without
+#   libdeflate), "error: bad
 #   .fai index <path>.fai", "error: unsupported FASTA <path>" (a byte read that the
 #   .fai layout does not explain), "error: .fai index does not match <path>"
 #   (fewer letters than the index promises), "error: FASTA read too large
@@ -258,3 +273,26 @@
   for hb: {E.texts_ok(command(pre, "--threads" <> x <> post), fasta, cs) == True{} : Bool}
   {launch(Norm.start(command(pre, "--threads" <> x <> post)), command(pre, "--threads" <> x <> post), fasta, vcf, cs)
     == launch(Norm.start(command(pre, post)), command(pre, post), fasta, vcf, cs) : Maybe<&2, Launch>}
+
+# The output options choose only how and where the text is written, never the
+# text. Wherever the parser expects an option (B.Args.expecting), adding one
+# output option o (B.Args.out_opt: -o PATH, -O T or the glued -OT) gives the
+# same paths and the same report (output bytes, messages, exit code) as the
+# same command line without it. The driver then writes the output bytes where
+# and how B.Args.output says (see law machine's comment). It follows from law
+# machine: parse gives the same Cfg with or without o where an option is
+# expected, and Opts.args does not record it.
+law output:
+  for pre: List<&2, String>
+  for o: List<&2, String>
+  for post: List<&2, String>
+  for fasta: String
+  for vcf: String
+  for cs: List<&2, String>
+  for he: {B.Args.expecting(pre) == True{} : Bool}
+  for ho: {B.Args.out_opt(o) == True{} : Bool}
+  for hf: {P.Fasta.plain(fasta) == True{} : Bool}
+  for h: {String.concat(cs) == vcf : String}
+  for hb: {E.texts_ok(command(pre, List.append(&2, String, o, post)), fasta, cs) == True{} : Bool}
+  {launch(Norm.start(command(pre, List.append(&2, String, o, post))), command(pre, List.append(&2, String, o, post)), fasta, vcf, cs)
+    == launch(Norm.start(command(pre, post)), command(pre, post), fasta, vcf, cs) : Maybe<&2, Launch>}
```

`examples.bend` (27 cases, all checked):

```diff
@@ -179,6 +179,95 @@
 def threads_refused() -> {B.Args.threads(["norm", "--threads", "8", "in.vcf"]) == None{} : Maybe<&2, Nat>}:
   {==}
 
+# --- Output options (-o, -O; law output) -----------------------------------
+
+# They change nothing Args.parse returns, and are not recorded in the header.
+def out_header() -> {B.Args.parse(["norm", "-Oz", "-f", "r.fa", "-o", "o.vcf.gz", "in.vcf"]) == Some{B.Cfg{B.Opts{True{}, 1000n, ["-f", "r.fa", "in.vcf"]}, "r.fa", "in.vcf"}} : Maybe<&2, B.Cfg>}:
+  {==}
+
+def out_sep() -> {B.Args.parse(["norm", "-f", "r.fa", "-O", "z9", "in.vcf", "-o", "-"]) == B.Args.parse(["norm", "-f", "r.fa", "in.vcf"]) : Maybe<&2, B.Cfg>}:
+  {==}
+
+# Refused: BCF (-O b, -O u, a .bcf path in any case), a level past 9, a level
+# on v, a bad type, a missing value; every -O must be valid.
+def out_Ob() -> {B.Args.parse(["norm", "-Ob", "-f", "r.fa", "in.vcf"]) == None{} : Maybe<&2, B.Cfg>}:
+  {==}
+
+def out_Ou() -> {B.Args.parse(["norm", "-O", "u", "-f", "r.fa", "in.vcf"]) == None{} : Maybe<&2, B.Cfg>}:
+  {==}
+
+def out_bcf() -> {B.Args.parse(["norm", "-f", "r.fa", "-o", "x.BCF", "in.vcf"]) == None{} : Maybe<&2, B.Cfg>}:
+  {==}
+
+def out_z10() -> {B.Args.parse(["norm", "-Oz10", "-f", "r.fa", "in.vcf"]) == None{} : Maybe<&2, B.Cfg>}:
+  {==}
+
+def out_v5() -> {B.Args.parse(["norm", "-Ov5", "-f", "r.fa", "in.vcf"]) == None{} : Maybe<&2, B.Cfg>}:
+  {==}
+
+def out_bad_first() -> {B.Args.parse(["norm", "-Ox", "-Oz", "-f", "r.fa", "in.vcf"]) == None{} : Maybe<&2, B.Cfg>}:
+  {==}
+
+def out_noval() -> {B.Args.parse(["norm", "-f", "r.fa", "in.vcf", "-o"]) == None{} : Maybe<&2, B.Cfg>}:
+  {==}
+
+# As a value, -o is that option's value; any word is a path for -o.
+def out_as_ref() -> {B.Args.parse(["norm", "-f", "-o", "in.vcf"]) == Some{B.Cfg{B.Opts{True{}, 1000n, ["-f", "-o", "in.vcf"]}, "-o", "in.vcf"}} : Maybe<&2, B.Cfg>}:
+  {==}
+
+def out_path_word() -> {B.Args.output(["norm", "-o", "--threads", "-f", "r.fa", "in.vcf"]) == Some{B.Sink{Some{"--threads"}, False{}, 6n}} : Maybe<&2, B.Sink>}:
+  {==}
+
+# B.Args.output: the extension decides when it names a type, else -O.
+def sink_default() -> {B.Args.output(["norm", "-f", "r.fa", "in.vcf"]) == Some{B.Sink{None{}, False{}, 6n}} : Maybe<&2, B.Sink>}:
+  {==}
+
+def sink_ext() -> {B.Args.output(["norm", "-f", "r.fa", "-o", "out.vcf.gz", "in.vcf"]) == Some{B.Sink{Some{"out.vcf.gz"}, True{}, 6n}} : Maybe<&2, B.Sink>}:
+  {==}
+
+def sink_ext_case() -> {B.Args.output(["norm", "-Ov", "-f", "r.fa", "-o", "OUT.Vcf.Bgz", "in.vcf"]) == Some{B.Sink{Some{"OUT.Vcf.Bgz"}, True{}, 6n}} : Maybe<&2, B.Sink>}:
+  {==}
+
+def sink_ext_plain() -> {B.Args.output(["norm", "-Oz9", "-f", "r.fa", "-o", "out.vcf", "in.vcf"]) == Some{B.Sink{Some{"out.vcf"}, False{}, 9n}} : Maybe<&2, B.Sink>}:
+  {==}
+
+def sink_other_ext() -> {B.Args.output(["norm", "-O", "z3", "-f", "r.fa", "-o", "out.gz", "in.vcf"]) == Some{B.Sink{Some{"out.gz"}, True{}, 3n}} : Maybe<&2, B.Sink>}:
+  {==}
+
+def sink_stdout_z() -> {B.Args.output(["norm", "-f", "r.fa", "in.vcf", "-Oz"]) == Some{B.Sink{None{}, True{}, 6n}} : Maybe<&2, B.Sink>}:
+  {==}
+
+def sink_dash() -> {B.Args.output(["norm", "-o", "out.vcf.gz", "-o", "-", "-f", "r.fa", "in.vcf"]) == Some{B.Sink{None{}, False{}, 6n}} : Maybe<&2, B.Sink>}:
+  {==}
+
+def sink_last() -> {B.Args.output(["norm", "-Oz1", "-f", "r.fa", "-Oz0", "in.vcf"]) == Some{B.Sink{None{}, True{}, 0n}} : Maybe<&2, B.Sink>}:
+  {==}
+
+def sink_refused() -> {B.Args.output(["norm", "-Oz", "in.vcf"]) == None{} : Maybe<&2, B.Sink>}:
+  {==}
+
+def out_threads() -> {B.Args.threads(["norm", "-Oz", "--threads", "8", "-o", "x.vcf.gz", "-f", "r.fa", "in.vcf"]) == Some{8n} : Maybe<&2, Nat>}:
+  {==}
+
+# The words of one output option (law output's B.Args.out_opt).
+def oo_o() -> {B.Args.out_opt(["-o", "a.vcf.gz"]) == True{} : Bool}:
+  {==}
+
+def oo_glued() -> {B.Args.out_opt(["-Oz5"]) == True{} : Bool}:
+  {==}
+
+def oo_sep() -> {B.Args.out_opt(["-O", "v"]) == True{} : Bool}:
+  {==}
+
+def oo_alone() -> {B.Args.out_opt(["-O"]) == False{} : Bool}:
+  {==}
+
+def oo_bcf() -> {B.Args.out_opt(["-o", "a.bcf"]) == False{} : Bool}:
+  {==}
+
+def oo_extra() -> {B.Args.out_opt(["-Oz", "x"]) == False{} : Bool}:
+  {==}
+
 # --- Whole runs ------------------------------------------------------------
 
 def fa() -> String:
```

`B.usage` becomes
`usage: framebender norm -f ref.fa [-c e|w] [-w N] [--threads N] [-o FILE] [-O v|z|z0-9] in.vcf`.
The old `> out.vcf` at the end is dropped, since `-o` now covers it.

## The driver (trusted; for the driver review)

### Effects (`main.bend`, `io64.c`, `io64.js`)

**`Io.out_open(file, path, z, level, n, vcf, ref) -> IO(U32)`.** Called once in `run.fai`, after
the FASTA, the .fai and the VCF are open and before the first step writes anything.
- So a run that fails on its inputs' names (usage, `cannot read`, `bad .fai`) creates no file.
  A run that fails while reading the VCF (`bad BGZF`) leaves the file it started.
- The output: stdout (`file` = 0), or the file `path` (bytes, as other paths).
- Plain or BGZF (`z`), at the level; with `n` compressor threads: `--threads` N, or 16.
- Answers:
  - 0;
  - 1: "error: cannot write <path>";
  - 2: "error: output is an input <path>";
  - 3: "error: no BGZF in this build <path>", in a build without libdeflate; `-` for stdout;
  - ENOMEM: "error: out of memory", when a libdeflate compressor cannot be allocated.
- An effect, not `put_bytes` choosing the file, so the C side owns the file descriptor and the
  BGZF state for the whole run.

**`Io.out_write(n, block) -> IO(U32)`** replaces `Io.write_block(1, n, a)` in `put_bytes`.
- Plain: the same synchronous full write as today, to fd 1 or the file.
- BGZF: hands the bytes to the writer (below).
- Answers 0, or the first write error seen so far.
- `Io.write_block` is then unused and is removed. `put` still writes the messages to fd 2, as
  today.

**`Io.out_close() -> IO(U32)`** at `P.Finish`, before `IO.exit`, whatever the machine's code.
- BGZF: finishes the last blocks, waits for the compressors and the writer, and writes the
  28-byte end-of-file block.
- A file: `close()`, and its error is checked.
- Answers 0 or an errno. A nonzero answer means "cannot write" (exit 2), after the machine's
  messages, which are already on stderr.

### The `-o` file

- **Opening:** `open(path, O_WRONLY | O_CREAT | O_CLOEXEC, 0666)`, without `O_TRUNC`. A new
  file gets mode 0666 less the umask, as shell redirection, `fopen` and htslib give.
  Symlinks are followed, and an existing file is overwritten, as bcftools does.
- **Not an input.** If the opened file is a regular file, `fstat` it and compare
  `(st_dev, st_ino)` with `stat` of the VCF path, the FASTA path and `FASTA.fai`.
  - The same file (through a symlink or a hard link too) is refused, *before* it is emptied:
    "error: output is an input <path>", exit 2.
  - Otherwise `ftruncate(fd, 0)`.
  - bcftools has no such check. `-o in.vcf` would destroy the input mid-read, and the check
    costs three `stat` calls.
- **Special files.** A file that is not regular (`/dev/stdout`, a FIFO, `/dev/null`) is
  neither compared nor emptied.
- **A failed run's partial file stays** (no deletion, no temporary file and rename), as with
  bcftools and with `> out.vcf`. What the file holds:
  - **The machine finishes, any exit code:** exactly the output text. With BGZF the file also
    ends with the end-of-file block, so `bgzip -dc` gives exactly what stdout would have held.
    For example, `-c e` stopping at a bad record writes the text up to it, as today.
  - **A driver error or a runtime stop mid-run** (`bad BGZF` on input, `cannot write`, `bend:
    out of memory`): the blocks written so far, *without* the end-of-file block. `bgzip -t`
    and htslib then report the file as truncated, so an unfinished `.vcf.gz` can be detected.
    Plain output gets a prefix of the text, as today.
  - A temporary file renamed at the end would protect pipelines better. But it fails for
    `-o /dev/stdout` and FIFOs, and it differs from bcftools. I do not propose it.

### BGZF writer

**Blocks: bgzip 1.24's text mode, exactly** (read in `htslib/bgzip.c`; reproduced in
`data/tmp/gz/pbgz_t.c`).
- **Windows.** The text is read in windows of 65280 bytes. A window is the bytes carried over
  from the last cut plus the next new bytes.
- **The header.** While in the header (lines starting with `#` or `@` at the start of the
  text), a window is cut after the header's last line, so the header's blocks hold no records.
- **Records.** Otherwise a window is cut after its last LF. A window with no LF (a line longer
  than 65280 bytes) is one full block.
- **The end.** At the end, the last, short window is cut by the same rule, and the bytes after
  its cut form one more block.
- **Block layout.** Each block is a gzip member with the `BC` extra field (BSIZE), deflated, then
  CRC32 and ISIZE. Level 0 writes a stored block by hand, as htslib does.

Consequences:
- **The compressed bytes depend only on the text and the level.** They do not depend on how the
  machine splits its output buffers, nor on `--threads`, nor on the number of compressor threads.
- **They match bgzip.** They are byte-identical to `framebender ... | bgzip -l L` on htslib 1.24
  with libdeflate 1.26 (prototype: chr22 at levels 0 to 9; the whole genome at the default).
- **Every record of up to 65280 bytes sits in one block, and the header is in its own blocks.**
  htslib's VCF writer (`bcftools -Oz`) arranges its blocks the same way.

**Zero copy.** Within one output buffer each window starts where the last one was cut, so a
compression job points straight into the Bend block, and nothing is copied.
- The exception is the first window of each `out_write`: the bytes carried from the previous
  buffer plus the new buffer's head, copied into a staging buffer of at most 65280 bytes.
- The cut search scans back over at most one line per block (forward over the header only),
  on the main thread. Its cost is negligible.

**Compressors.** n threads (`--threads` N, default 16), each with its own libdeflate compressor
at the mapped level.
- They take jobs from a FIFO.
- Each compresses its window into its own buffer of at most 65536 bytes. If libdeflate does not
  fit (it cannot, for 65280 bytes with 65510 of room), the block is written stored.

**Writer thread.** It writes the finished blocks strictly in job order, with full `write()`
calls (retrying on EINTR), so the main thread never waits on the disk or the pipe.
- The first error is recorded and later blocks are dropped.
- `out_write` and `out_close` report the error. "cannot write" can therefore come a few steps
  later than today, after those steps' messages.
- SIGPIPE behaves as today (the default action).

**Freeing the Bend blocks.** A block handed to `out_write` stays alive until all its jobs are
compressed. It is freed (`blk_free`) on the main thread, at the next `out_write` or at
`out_close`.
- **Double buffering.** `out_write` first waits until the *previous* buffer is fully compressed,
  frees it, and then queues the new one. Buffer k is compressed while the machine computes
  step k+1.
- **Main-thread time** is the cut search plus at most one 65280-byte copy per step, and a wait
  only when compression falls behind the machine.
- Helper threads already read straight into Bend blocks (the read-ahead), and the heap patch
  lets a large block freed on one thread be reused by any, so holding a block across effects is
  the existing pattern, reversed.

**Memory**, on top of today's:
- about one extra output buffer alive (≈ N × 3.5 MB: 56 MB at N = 16, like the read-ahead);
- the compressed blocks waiting to be written (about 1/19 of the text in flight);
- n libdeflate compressors (≈ 1 MB each at the default level, more at 8 and 9);
- n × 64 KiB of buffers.

Expected: 330 MB becomes 400 MB at the default. To be measured in step 2. Memory grows with N,
which is already stated outside law machine.

**`--threads 1`:** a single compressor thread. Compressing the whole genome at the default level
takes 1.85 s on 16 threads, so on one thread it is on the order of 15 to 30 s. `-Oz --threads 1`
will therefore be much slower than the plain run's 6 s; `-Oz1` is about 2.4 times cheaper. "N limits the work at once" is what `--threads`
promises, so I keep compressors = N and document the cost. The alternative would be compressors
= max(N, 4).

**The runtime constructor** (`io64_threads_of`, `io64.c`) copies the parser's grammar to set
Bend's worker threads before `main`. It must learn the new options, or it refuses those lines
(fail-safe: the runtime keeps one worker per CPU).
- `-o` takes any value and refuses `.bcf` in any case.
- `-O` takes `v`, `z` or `z0` to `z9`.
- A glued `-O...` is checked the same way.

This goes to the driver review with the rest.

**Not designed out:**
- **`-W` (an index).** The writer knows each block's compressed offset and the text offset where
  it starts, so a later `.csi` or `.tbi` writer can map record offsets to virtual offsets. The
  record coordinates would come from the driver, or from a proven indexer. `Drv` gains a field.
- **BCF.** `OType` gains a case. `-Ob`, `-Ou` and `.bcf` are refused today, so adding BCF
  changes no accepted command line.

## Test plan (step 2)

`test/out.sh new_binary` (new), on:
- the edge cases;
- the batch-boundary cases (`test/gen_par.py`) and the generated cases;
- chr22 and the scrambled file;
- the whole genome, plain and `.vcf.gz`;
- the 1000 Genomes chr22 file (records of 14 KB).

Each case runs on the normal build and on the small-piece builds (300, 1,000 and 70,001 bytes).

**Byte identity.** For each case, `-c e` and `-c w`, `--threads` 1, 2, 3, 7, 16, 32 and 128 at
three positions, the option at three positions, and the `-o`/`-O` forms (`-o x.vcf.gz`, `-Oz`
to stdout, `-O z`, `-Oz0`, `-Oz1`, `-Oz9`, `-o x.vcf -Oz`, `-o -`):
- stderr and the exit code are those of the same command without the output options;
- `bgzip -dc` of the output (or the plain file) is byte for byte the plain stdout;
- the file is byte-identical to `plain | bgzip -l L`. The exception is output that bgzip does
  not recognise as text (empty output, binary bytes): bgzip then cuts at fixed 65280 bytes, and
  those cases are listed;
- the compressed file is the same at every `--threads`. This follows from the previous check,
  and is checked directly too;
- `bgzip -t` passes; `htsfile` says BGZF VCF; `bcftools view -H | wc -l` gives the right count;
  `tabix -p vcf` accepts the sorted, successful outputs, and `tabix` queries match `grep`.

Edge cases:
- **Empty output:** only the end-of-file block.
- **Header and record size:**
  - a header longer than 65280 bytes;
  - a record longer than 65280 bytes (generated);
  - a record of exactly 65280 bytes;
  - an output that ends without a LF;
  - an input that ends at a block boundary.
- **Failures:**
  - a `-c e` stop mid-file: a complete file, equal to the plain run;
  - a `.vcf.gz` input cut mid-file: exit 2 "bad BGZF", and the output has no end-of-file block,
    so `bgzip -t` fails;
  - `bend: out of memory` under a memory cap: the same.

**Files and errors:**
- `-o` to a new file, with umask 022 and with umask 077: mode 0644 and mode 0600;
- `-o` over an existing larger file: it is truncated, and its mode is kept;
- `-o` to a directory, to a missing directory, or without permission: "cannot write <path>",
  exit 2, and no file is created;
- `-o` naming the VCF, the FASTA or the .fai (directly, through a symlink, through a hard link):
  "output is an input", exit 2, and the input's md5 is unchanged;
- `-o /dev/stdout`, a FIFO, `/dev/null`;
- a full disk:
  - `-o /dev/full`;
  - stdout redirected to `/dev/full` with `-Oz`;
  - an RLIMIT_FSIZE limit with SIGXFSZ ignored (`trap '' XFSZ; prlimit --fsize=...`), with the
    limit set inside the header, mid-file, and at the end-of-file block;

  each must give "cannot write ...", exit 2;
- a closed pipe (`| head -c 100`): exit 141, as today.

**Usage errors:**
- `-Ob`, `-Ou`, `-O b`, `-Oz10`, `-Ov5`, `-O5`, `-Ox`;
- `-O` at the end, `-o` at the end;
- `-o x.bcf`, `-o X.BCF`;
- `-Ox -Oz` (every `-O` must be valid).

Each must print the usage and exit 2.

**The constructor:** the threads a run starts with `-o` and `-O` on the line, as
`test/threads.sh` checks.

**Gate:** `check.sh` through `test/bcheck.sh`; `test/same.sh` and `test/par.sh` (unchanged output
without the new options); `test/threads.sh`.

**Timing** (under the bench lock, pinned, interleaved), with time and peak RSS:
- whole genome to `.vcf.gz` at the default, `-Oz1` and `-Oz9`, and plain `-o x.vcf`;
- `--threads` 1, 4, 8, 16 and 32;
- against `bcftools norm -Oz --threads 16`, `bcftools norm -Oz` and `bcftools norm | bgzip -@16`;
- the same on the 1000 Genomes file.

## What the proofs and examples need, and the size of the work

**Examples:** the 31 cases above, already checked on the scratch copy. `examples_machine.bend`
gets `m_output`, which is `m_pieces` with `-Oz -o x.vcf.gz` and `-O v`, expecting the same
`Launch`.

**Proofs:**
1. **`proof_f_args.bend`: the thread count becomes `drv`.**
   - `unthr` becomes `undrv` (`drv := Drv.none()`), and `inv`/`tin` read `Drv.thr`.
   - Every `match` on `Pend` gains `POut` and `PType` (8 sites, plus 1 each in
     `proof_b_bud_start.bend` and `proof_b_drive_start.bend`).
   - `Args.word`'s pick chain grows by three branches (`w5` to `w8`, with the pick lemmas for
     each).
   - New step lemmas for `-o` and `-O`: they keep `keep` and `kl`, preserve `inv`, and are
     blind to `drv`.
   - About 250 changed lines and 150 new.
2. **`out_words` and `parse_out`** (same file): from a state where an option is expected, the
   words of `out_opt(o)` change only `drv`. The proof goes by the three shapes of `o`, then
   `go_append` and `done_same`. About 150 lines.
3. **`proof_f_output.bend`** (new): law `output` from `parse_out`, `same_parse` (imported from
   `proof_f_threads.bend`) and a bytes lemma for dropping a list of words (`ab_drop`, for a
   list). About 120 lines. `PROOF.bend` forwards `M.output`.
4. **Optional: `output_ok`.** `Args.output` is `Some` exactly when `Args.parse` is. The driver
   does not need it: it calls `Args.output` only after `Norm.start` gave `Begin`, and treats
   `None` as stdout plain. The level's bound (≤ 9) is not proven: proving `Pos.read` of one
   digit is ≤ 9 needs U32 lemmas. `io64.c` clamps instead (`level > 9 → 9`, unreachable).

**Driver:**
- `main.bend`: about 40 lines (`Sink` into `Io`; `out_open`, `out_write`, `out_close`; error
  messages);
- `io64.c`: about 350 lines (the cut rule, the job FIFO, the compressors, the writer thread,
  open/check/truncate/close, the constructor's grammar);
- `io64.js`: plain output only; BGZF is refused there with "no BGZF in this build".

`build.sh` does not change: libdeflate is already linked, and its compressor is in the same
library.

**Docs:**
- the README (Run: `-o`, `-O`, the extension rule, the default level and `-Oz1`; Results: the
  new timings; the differences from bcftools);
- `docs/LAWS.md` (law `output`, and the trusted writer under "What the laws do not cover");
- `docs/DEVELOPMENT.md` (`test/out.sh`);
- `NOTES.md`.

**Size:** about 1.5 to 2 days of agent work, like `--threads`. Most of it is the parser proofs
(mechanical) and the writer with its tests.

## Prototype measurement (scratch)

**Setup.**
- `data/tmp/gz/pbgz_t.c` is a 16-thread libdeflate BGZF writer that cuts blocks as bgzip 1.24
  does, run as a separate process at the end of a pipe. The in-driver writer saves the 2.8 GB
  pipe copy but competes for the same CPUs, so expect about the same time.
- Whole genome (`data/hg002.all.vcf`), `-c w`, to a file deleted before each run.
- Pinned to CPUs 0–15, `nice -n 19`, under `flock data/tmp/bench.lock`, interleaved, 2 rounds
  (`data/tmp/gz/bench.py`; the raw lines are in `data/tmp/gz/bench1.txt` and `bench2.txt`).
- "fb" is this branch's binary (`build.sh`); bcftools and bgzip are 1.24.
- Every framebender output had the same md5 in each configuration.
- "fb | pbgz 16 L7" and "fb | bgzip -@16" gave the same file (md5 `b269909de524`).

| run | wall | output size |
|---|---|---|
| fb, plain | 1.80–1.83 s | 2,836.8 MB |
| bcftools, plain | 7.95–7.99 s | 2,836.9 MB |
| **fb \| pbgz 16 threads, default level (libdeflate 7)** | **3.01–3.02 s** | 150.2 MB |
| fb \| pbgz 16 threads, htslib level 1 | 2.37–2.39 s | 253.4 MB |
| fb \| pbgz 8 threads, default level | 3.26–3.28 s | 150.2 MB |
| fb \| bgzip -@16 | 3.22–3.23 s | 150.2 MB |
| **bcftools norm -Oz --threads 16** | **6.11–6.24 s** | 150.2 MB |
| bcftools norm -Oz | 14.41–14.48 s | 150.2 MB |
| bcftools norm \| bgzip -@16 | 6.65–6.66 s | 150.2 MB |
| pbgz 16, default level, on the plain file alone | 1.84–1.85 s | |
| pbgz 16, level 1, on the plain file alone | 0.78 s | |
| bgzip -@16 on the plain file alone | 1.96–1.97 s | |

What the numbers say:
- **The lead holds, smaller.** Against `bcftools norm -Oz --threads 16` it is 6.2 s to 3.0 s
  (2.0×), where plain output is 4.4×. bcftools gets *faster* with `-Oz` than plain (8.0 s to
  6.2 s), since writing plain text is part of its cost.
- **Compression is the new cost.** It takes about 1.85 s of 16-thread work on its own, on the
  same 16 CPUs as the normalizer. Overlapped, it adds about 1.2 s to the plain run.
  - htslib level 1 adds 0.6 s, for a file 1.7 times larger.
  - 8 compressor threads are 0.25 s slower than 16.
- **Peak memory** was not measured meaningfully here. The method floors at 47–48 MB, the measuring
  Python's footprint carried across `exec`, so every small process shows that. The prototype
  holds about 16 MB of buffers. Step 2 measures the driver itself.
- **The default level stays htslib's.** The lead holds with it, it matches the bytes
  of `bgzip` and the size of `bcftools -Oz`, and `-Oz1` is there for speed.

## Questions for the reviewers

1. **The extension wins over `-O`** (bcftools 1.24's behaviour). Should framebender copy it?
   The alternative is to refuse a conflict (`-Oz -o x.vcf`). Then whether a line is accepted
   would depend on two options together, and law `output` would need a premise on the whole
   line instead of one option.
2. **`-o` and `-O` are not recorded in the header.**
3. **A BGZF file is completed (end-of-file block) whenever the machine finishes**, even with a
   nonzero code (a `-c e` stop). It is left unterminated only on a driver or runtime failure.
4. **The default level:** 6 on htslib's scale (libdeflate 7). The alternative is 1 for speed.
5. **`-o` refusing a path that is an input**, a check bcftools lacks.

## Step 2: implemented, proven, tested (2026-10-29)

The law review (`reviews/{claude,gpt,grok}-compress-law.md`, decisions in
`reviews/responses-compress-law.md`): all three accept law `output` and the grammar. The twelve
decisions, as implemented:

1. **The end-of-file block only for exit code 0.** A `-c e` or UNSORTED stop writes every block of
   the text, then no end-of-file block. Law machine's comment: "a BGZF file is complete exactly
   when the run succeeded"; decompressed, the file is the output bytes written so far.
2. **Nothing after a failed write.** The writer keeps the first error, writes nothing more (it
   still takes the blocks, so nobody waits), and `Io.out_write` and `Io.out_close` answer it:
   "cannot write <path>", exit 2, no end-of-file block. Short writes and EINTR are retried. A
   driver error mid-run exits (2) with the threads running: no end-of-file block.
3. **Sticky level, as in bcftools 1.24** (checked again: `-Oz0 -Oz` is level 0, `-Oz9 -Ov -o
   x.vcf.gz` is BGZF level 9, `-Oz9 -o x.vcf` plain). `Drv` keeps the type (`z`) and the level
   (`lvl`) apart: `Drv{thr, out, z, lvl}`; a `-O` without a digit leaves `lvl`.
4. **The `-o` file is opened lazily**, at the first `Io.out_write` (or at `Io.out_close` for an
   empty output). The first write comes after the first VCF piece was read, so a missing or
   unreadable VCF, a plain-gzip VCF, a missing FASTA or a bad `.fai` leave an old file unchanged
   (tested).
5. **Identity from open descriptors.** `Io.read_block` records `fstat` of each stream it opens
   (the `.fai`, the VCF), `Io.out_set` `fstat` of the open FASTA, and the open output is compared
   with those and with `fstat(2)` (stderr) before `ftruncate`.
6. **Bounded queues.** At most 2 × N blocks (at least 4) are taken by a compressor and not yet
   written; a slow writer stops the compressors, and `Io.out_write` returns only once its
   buffer's blocks are all written (a change from the design: see "One buffer at a time"
   below). Tested with a reader that waits 20 s (below).
7. **The carried tail is copied** into the writer's own window buffer before the buffer is freed;
   at `Io.out_close` the last window and the tail are queued, everything is written, the threads
   joined, and only then the end-of-file block.
8. **`output_ok` is proven** (`proof_f_out.bend`): `Args.output` is `Some` exactly when
   `Args.parse` is. The driver treats a `None` after `Norm.start` began as "internal error: no
   output" (exit 2), never as stdout.
9. **Tests, corrected**: plain outputs against the plain stdout, BGZF ones against `bgzip -l L`
   (without the end-of-file block when the code is not 0), the generated block-cut cases,
   incompressible data, the round trip, the sanitizers, failed writes checking the file.
10. **Comments**: law `output`'s comment says it covers the machine's report, not the driver's
    own `-o` errors, and that compressed output can run out of heap where plain does not; `Sink`
    says its level is unused when `z` is False; `docs/LAWS.md` has the one-sentence rule.
11. **Examples**: missing `-O` value, glued `-oFILE`, an invalid first `-o`, repeated `-O` with
    levels, `-o` as a bare VCF path versus `./-o`.
12. **Notes**: 27 examples in the draft, not 31; "Not taken from bcftools" completed (above).

### Files

- **Science and contract (as reviewed, with decisions 3, 10 and 11):** `types.bend` (the parser:
  `Drv`, `OType`, `-o`, `-O`, `Args.output`, `Args.out_opt`), `MACHINE.bend` (law `output`, law
  machine's comment), `examples.bend` (35 new cases: the draft's 27 and decision 11's 8).
- **Proofs:**
  - `proof_f_args.bend`: the thread count became the record `drv` (`unthr` now erases all of
    it), two new `Pend` cases, three new branches of `Args.word` (`w5` to `w8`), and the one-step
    lemmas for `-o` and `-O` (`typ_kl`, `typ_ab`, `typ_inv`, `out_inv`, `typ_un`). +188 −35.
  - `proof_f_out.bend` (new, 437 lines): `pre_O` (a word that starts with `-O` is `-O` and the
    rest), `glued`, `two_k` (the two-word options, split on whether the first word is `-o`),
    `out_words` (the words of `out_opt` change only `drv`), `parse_out`, law `output` (from
    `FT.same_parse`, as law `threads`), and `output_ok`.
  - `proof_b_bud_start.bend`, `proof_b_drive_start.bend`: the two new `Pend` cases.
  - `PROOF.bend` forwards `M.output`.
- **Driver (trusted, for the driver review):**
  - `main.bend`: `Io.out_set`, `Io.out_write`, `Io.out_close` (replacing `Io.write_block`), the
    `-o` path in the loop's state for the error messages, `B.Args.output` read at the start.
  - `io64.c`: the output section (about 450 lines: lazy open and the identity check, the bgzip
    cut, the job ring, N compressors, the writer thread), the stream identities in
    `Io.read_block`, and the constructor's grammar (`-o`, `-O`, glued `-O…`).
  - `io64.js`: the three effects (BGZF refused there).
- **Tests:** `test/out.sh` (new), `test/gen_out.py` (new).
- **Docs:** README (Run, differences), `docs/LAWS.md`, `docs/DEVELOPMENT.md`.
- **Not changed:** `build.sh` (libdeflate's compressor is in the library already linked),
  `examples_machine.bend` (its cases pass the checker's 4 GB cap, so no `m_output` was added;
  `test/out.sh` checks the same thing on real runs).

### One buffer at a time: a change from the design

The design kept each output buffer after `Io.out_write` returned, freeing it at the next call,
so that its blocks were compressed while the machine computed the next step. Measured:
- **Whole genome:** 3.00–3.10 s kept, 3.05–3.12 s without (2 rounds); peak RSS the same
  (335 MB).
- **1000 Genomes chr22 (`.vcf.gz`):** 14.0–15.1 s kept, 14.8–15.4 s without; 333 MB against
  318 MB.
- **300 MB of incompressible 64 KB records** (`data/tmp/gz/big.py`): 956–963 MB kept, 700–706 MB
  without (plain: 686–691 MB). Keeping only the buffers of up to 8 MB still gave 951 MB: holding
  any heap block across a step made Bend's heap grow on this file. The level did not matter
  (`-Oz0`: 952 MB).

So `Io.out_write` now compresses its buffer on the N threads, waits until its blocks are written,
and frees it, as the plain path does. That costs about 3% in time and bounds the memory: no heap
block is held across a step, and the held-block bookkeeping (and its free at the next call) is
gone.

### Checks

All through `test/bcheck.sh`, on the final tree:
- `examples.bend --check-only`: 17 TODOs (the imported laws, now with `output`), no errors; 106
  examples (35 new).
- `main.bend --check-only`: 88 defs rely on unsafe or foreign code (79 before: the new driver
  defs).
- `PROOF.bend --check-only`: ALL PROOFS CHECK. `PROOF.bend --verdict`: ALL PROOFS CHECK.

### Tests

Builds: NEW (this tree, `build.sh`), the 300, 1,000 and 70,001-byte piece builds (a `CC` wrapper
replacing `3670016ull`, `data/tmp/gz/cc_piece.sh`), and REF (step 1's build of this branch,
`data/tmp/gz/fb`). Scratch in `data/tmp/gz/`; `same.sh` and `par.sh` ran as private copies there,
so `data/tmp/rw` and `data/tmp/par` are untouched.
- **`test/same.sh`, `test/par.sh`, `test/threads.sh`** (NEW against REF, plain output): ALL
  IDENTICAL, 128, 312 and 2,128 runs, and USAGE ERRORS OK, on each of the four builds.
- **`test/out.sh`** (new), in full on each of the four builds, after the last change: ALL
  IDENTICAL (1,680 runs: 84 cases × `-c e`/`-c w` × 10 output forms, `--threads` 1 to 128 at
  three positions), LEVELS 0-9 AND TOOLS OK (chr22 at every level against `bgzip -l L`; `bgzip
  -t`, the end-of-file block, `tabix -p vcf`, a `tabix` query against `awk`, `bcftools view -H`),
  FAILURES OK, FILES OK, USAGE ERRORS OK, ROUND TRIP OK.
  - The 84 cases include `test/gen_out.py`'s: records of 65279, 65280, 65281, 130560 and 200000
    bytes; CRLF; incompressible records of 60000 and 300000 bytes; a last line without LF; a
    header alone; a header of 3,000 contig lines; headers ending exactly at the first and at the
    second block boundary.
  - Failures: the VCF missing, a plain-gzip VCF, the FASTA missing, the VCF a directory: exit 2,
    an old `-o` file unchanged. A `.vcf.gz` cut mid-file: exit 2, no end-of-file block, the text
    a prefix of the plain run's. `/dev/full` (as `-o`, plain and BGZF, and as stdout): "cannot
    write", exit 2. A file size limit (`prlimit --fsize`, SIGXFSZ ignored) at 1,000 bytes (inside
    the header block), 300,000, exactly before the end-of-file block, and 10 bytes before the
    end: "cannot write <path>", exit 2, the file a prefix of bgzip's bytes (or of the plain
    text), no end-of-file block. A closed pipe: "cannot write", exit 2, as with plain output
    (Bend's runtime ignores SIGPIPE; the step-1 notes' "SIGPIPE" was wrong).
  - Files: `-o` naming the VCF, a symlink to it, the FASTA, the `.fai`, a hard link to the VCF,
    and stderr's file: "output is an input", exit 2, inputs unchanged. A directory, a missing
    directory, an unwritable one: "cannot write <path>", no file. Modes 644 and 600 under umask
    022 and 077; an existing larger file emptied and its mode (640) kept; `/dev/stdout`,
    `/dev/null`, a FIFO.
  - Threads seen on chr22 with `--threads 3`: 7–8 plain, 11–12 with `-Oz` (3 compressors and the
    writer); the constructor still limits Bend's workers when `-o` and `-O` are on the line.
- **Large inputs** (`data/tmp/gz/big.py`): `-Oz` byte for byte `plain | bgzip -@16`, the same
  stderr, exit 0, on the whole genome (plain and `.vcf.gz` input, and `--threads 3`), the 1000
  Genomes chr22 file (14.8 GB of text), and 300 MB of incompressible 64 KB records.
- **Stalled reader** (20 s before the first read): whole genome 338 MB against 341 MB unstalled;
  incompressible 703 against 702 MB; the same bytes.
- **Sanitizers** (`data/tmp/gz/san.sh`: levels 0 and 9, `--threads` 1 and 128, a stalled pipe,
  `/dev/full`, a size limit, the generated cases, a cut VCF): ThreadSanitizer reports no race; its
  one report is a thread leak of the existing VCF read-ahead helper on the "bad BGZF" exit
  (`io64_ahead_start`, not the writer). ASan: no error (with leak detection off; with it, only a
  72-byte allocation in the runtime's `main`).

### Timing

Pinned to CPUs 0-15, `nice -n 19`, under `flock data/tmp/bench.lock`, interleaved, output to a
file deleted before each run (`data/tmp/gz/bench3.py`; raw lines in `data/tmp/gz/time_*.txt`).
Peak RSS per process from `wait4`. Every framebender `-Oz` run of HG002 gave md5 `b269909de524`,
the same as `framebender | bgzip`.

HG002 whole genome, 2 rounds at a load average of 2.5 to 3.5 (`time_hg002b.txt`):

| run | wall | peak RSS | file |
|---|---|---|---|
| framebender plain | 1.75–1.81 s | 328–331 MB | 2,836.8 MB |
| framebender `-Oz` | 2.90 s | 336–338 MB | 150.2 MB |
| framebender `-Oz1` | 2.10–2.12 s | 333–334 MB | 253.4 MB |
| bcftools plain | 7.97–7.99 s | 12 MB | 2,836.9 MB |
| bcftools `-Oz --threads 16` | 6.32–6.46 s | 18 MB | 150.2 MB |
| bcftools `-Oz` | 14.33–14.53 s | 12 MB | 150.2 MB |
| bcftools `\| bgzip -@16` | 6.71–7.01 s | 12 + 14 MB | 150.2 MB |

The same at a load average of 5 to 8 (3 rounds, `time_hg002.txt`): framebender `-Oz` 3.14–3.18 s,
`-Oz1` 2.26–2.30 s, `-Oz9` 72.2–76.3 s (355–362 MB, 140.9 MB); bcftools `-Oz --threads 16`
7.19–7.81 s, `-Oz` 15.7–16.6 s, `| bgzip -@16` 7.74–8.09 s. `--threads` with `-Oz` (2 rounds, same
load, `time_thr.txt`): 1: 15.1–15.7 s, 43–44 MB; 1 with `-Oz1`: 9.9–10.1 s; 4: 4.76–4.81 s,
121–127 MB; 8: 3.12–3.15 s, 196–200 MB; 32: 3.28–3.30 s, 610–612 MB.

1000 Genomes chr22 `.vcf.gz` (`time_kg.txt`): framebender plain 7.20–7.79 s, `-Oz` 13.80–13.99 s,
`-Oz1` 8.02–8.03 s, 306–320 MB each (2 rounds); bcftools `-Oz --threads 16` 65.2 s (31 MB),
`bcftools | bgzip -@16` 74.2 s (one run each).

What the numbers say:
- **The lead holds:** 2.9 s against 6.3–6.5 s (2.2×) on the whole genome, 14 s against 65 s
  (4.7×) on the cohort file. bcftools is faster with `-Oz --threads 16` than plain (8.0 s), as in
  step 1.
- **Compression costs the CPUs it takes:** +1.1 s on the whole genome, +6.5 s on the cohort file
  (14.8 GB of text). `-Oz1` cuts that to +0.3 s and +0.6 s for a file 1.7 and 1.3 times larger.
- **Memory hardly moves:** +8 MB at the default; one buffer at a time keeps it there.
- **`--threads 8 -Oz` is as fast as the default** (3.1 s) at 200 MB: the compressors need the
  CPUs that Bend's extra workers would take.
- **`--threads 1 -Oz` is 15 s**, about bcftools' single-threaded `-Oz`; `-Oz1` makes it 10 s.
- **Level 9 is libdeflate's level 12** (htslib's mapping), 25 times slower than the default for
  6% less: documented, not changed, since it gives bgzip's bytes.

### Open, for the driver review

- The writer in `io64.c` (the bgzip cut copied from htslib's `bgzip.c`, the job ring, the
  compressors and writer, the lazy open and the identity check), and `main.bend`'s output plumbing.
- The constructor's grammar for `-o` and `-O` (`io64_threads_of`, with `io64_ends_ci` and
  `io64_otype`).
- One buffer at a time instead of the designed overlap (above).
- A driver error mid-run exits with the compressor and writer threads running (no end-of-file
  block, by design); ThreadSanitizer's only report is the read-ahead helper's, at that exit.
- `io64_out_set` clamps the level to 9 and the threads to 128; neither is reachable
  (`Args.otype`, `threads_ok`).

## Driver review 8 (2026-10-29)

Reports `reviews/{claude,gpt,grok}-driver8.md`, decisions `reviews/responses-driver8.md`. None
accepted; every finding was in the trusted output path. As fixed:

1. **A pipe or FIFO input named by `-o` is refused.** `io64_out_open` compares the opened output
   (device and inode) with the VCF, the FASTA and the `.fai` whatever its type, and with stderr
   when stderr is a regular file or a FIFO (not a terminal or other character device, so `-o
   /dev/stdout` still works). A match closes the new descriptor: "output is an input", exit 2.
   Only a regular file is emptied. Before: `cat in.vcf | fb ... -o /dev/stdin /dev/stdin` and one
   FIFO as both VCF and `-o` hung (the driver held the write end, so the VCF never ended).
2. **`SIGXFSZ` is ignored** from the output's open on, so a write past a file size limit fails with
   `EFBIG`: "cannot write <path>", exit 2, no end-of-file block. Before, the signal killed the run
   (status 153); `test/out.sh`'s `trap '' XFSZ` had hidden it and is gone (its stderr now goes
   through a pipe, as the limit applies to a stderr file too).
3. **A failed `close` after the end-of-file block takes the block back.** `io_out_close_run`
   remembers the file offset before the block; if `close` of a regular `-o` file then fails, it
   opens the path again and truncates it to that offset, and reports "cannot write <path>". A pipe
   cannot take bytes back: law machine's comment says so.
4. **`test/out.sh` exits with its result** (`exit "$bad"`).
5. **The final carried bytes as bgzip writes them.** `io64_out_text` records where the last full
   window ended (`wend`); at the end, if no byte came after it, the carried bytes are one block,
   uncut, as bgzip's last `bgzf_write`; otherwise the last short window is cut as before. The two
   differ only for a text that does not end in LF, which the machine never writes; the claim
   "bgzip's bytes for any text" now holds anyway. `test/gen_out.py`'s `tailwin.vcf` makes the whole
   output exactly one window, the records carried past the header's cut to the end.
6. **Comment:** law machine's comment says a BGZF file decompresses to a prefix of the output
   bytes, all of them when the machine finished (after a driver error the carried bytes are not
   written).
7. **Tests** (`test/out.sh`): a transient failure (stdout a non-blocking pipe that fills while
   its reader waits 2 s: one `EAGAIN`) gives "cannot write", exit 2, and a prefix of bgzip's
   bytes with no end-of-file block; the injected `close` failure (an `LD_PRELOAD` shim, built by
   the script) leaves bgzip's bytes less the end-of-file block; the size limit without the trap;
   `-o /dev/stdin` and `-o /proc/self/fd/0` with the VCF on a pipe, one FIFO as VCF and `-o`, and
   `-o /dev/stderr` with stderr a FIFO, all refused without a hang; section 6 now fails if a run
   with `--threads 3` and `-o`/`-O` shows more than 12 threads (16 with `-Oz`); section 7
   (`NOLIB=binary`) runs a `bend main.bend -o` build: "no BGZF in this build <path>" (and `-` for
   stdout), the old file untouched, plain `-o` output right.

Not on the hot path (one assignment per window, one `signal` call), so not re-timed.

Checks and tests after the fixes (all on the final tree):
- Gate through `test/bcheck.sh`: `examples.bend` 17 TODOs (the imported laws), `main.bend` 88 defs
  on unsafe or foreign code, `PROOF.bend` ALL PROOFS CHECK with `--check-only` and with
  `--verdict`.
- `test/out.sh` in full, exit 0, on the normal build (with `NOLIB=` the `bend main.bend -o` build)
  and on the 300, 1,000 and 70,001-byte piece builds: ALL IDENTICAL (1,700 runs each: 85 cases
  now, with `tailwin`), LEVELS 0-9 AND TOOLS OK, FAILURES OK, FILES OK, USAGE ERRORS OK, ROUND TRIP
  OK, NO-BGZF BUILD OK (normal build), threads within the bounds.
- The plain path's open and close changed, so `same.sh`, `par.sh` and `threads.sh` (private
  copies, NEW against step 1's build): ALL IDENTICAL, 128, 312 and 2,128 runs, USAGE ERRORS OK.
  The constructor did not change, so the small-piece builds were not rerun with these.
- Sanitizers (`data/tmp/gz/san.sh`): ThreadSanitizer's one report is still the read-ahead
  helper's thread leak at the "bad BGZF" exit; ASan none.

### Round 2 (decisions 8 to 10)

Grok and Claude accept; GPT had two should-fix items in the take-back after a failed `close`.

8. **The take-back checks identity and is best effort.** `io64_out_open` keeps the `-o` file's
   device and inode; after a failed `close`, `io_out_close_run` reopens the path and truncates only
   if `fstat` of the reopened descriptor matches, never another file the path now names. When the
   take-back cannot be done (the path changed, or cannot be opened again, as under umask 0777),
   the error is still reported (exit 2) and the file keeps its end-of-file block. Law machine's
   comment, `io64.c` and `docs/LAWS.md` say "best effort". (A duplicate of the descriptor kept
   until the close would work under umask 0777 too, without a path lookup; the decision named
   the reopen, which is what is implemented.)
9. **stderr is compared only when it is a regular file.** `-o /dev/stdout 2>&1 | tail` and `-o
   /dev/stderr` with stderr a FIFO now run (exit 0, output and messages on the one pipe); the test
   is an accepted case now, and a second one pipes `-o /dev/stdout 2>&1` through `cat`.
10. **Tests** (`test/out.sh`):
    - an `LD_PRELOAD` `write()` shim fails the 3rd write to the `-o` file once with `EIO` and lets
      later ones through: exit 2, "cannot write <path>", the file non-empty, a prefix of bgzip's
      bytes (BGZF) or of the plain text, no end-of-file block (a writer that went on would leave a
      gap);
    - the close shim can also move the file away and point its path at another file
      (`FB_CLOSEFAIL_REPOINT`): that file is unchanged and the moved file keeps its end-of-file
      block; and a take-back that fails (umask 0777): exit 2, the file keeps the block;
    - `gen_out.py` says `tailwin` runs the uncut end but cannot tell it from cutting again (the
      machine ends every text with LF). No direct C test of the cut on a text without a final LF:
      `io64.c`'s writer needs the generated runtime's types, so a standalone harness is not
      simple; the case is unreachable from the machine's output.

Checks: the gate through `test/bcheck.sh` (17 TODOs in `examples.bend`, 88 unsafe or foreign defs
in `main.bend`, ALL PROOFS CHECK with `--check-only` and `--verdict`); `test/out.sh` in full on
the normal build with `NOLIB=`: ALL IDENTICAL (1,700 runs), LEVELS 0-9 AND TOOLS OK, FAILURES OK,
FILES OK, USAGE ERRORS OK, ROUND TRIP OK, NO-BGZF BUILD OK, OUT OK, exit 0.

### Decision 8, amended: the take-back through a duplicate descriptor

Adopted in place of the reopen by path (`reviews/responses-driver8.md`, end): `io64_out_open`
keeps a duplicate of a regular `-o` file's descriptor (`fcntl(F_DUPFD_CLOEXEC)`, failing the open
like any other error if it cannot be had) from the open until `Io.out_close`. After a failed
`close` of the file, the end-of-file block is cut off through the duplicate (the same open file,
whatever the path names by then), then the duplicate is closed; the stored device and inode and
the reopen are gone. The take-back is exact for regular files, also under umask 0777; a pipe still
cannot take bytes back. The duplicate's own close comes after the file's, which flushed the bytes:
its failure is not reported (nothing left to write, no descriptor left to take the block back
with). Law machine's comment, `io64.c` and `docs/LAWS.md` no longer say "best effort".

Tests (`test/out.sh`): the umask 0777 case now expects bgzip's bytes without the end-of-file
block; the re-pointed path leaves the other file untouched, and the moved file is cut.

Checks: the gate through `test/bcheck.sh` (17 TODOs in `examples.bend`, 88 unsafe or foreign defs
in `main.bend`, ALL PROOFS CHECK with `--check-only` and `--verdict`); `test/out.sh` in full on the
normal build with `NOLIB=`: ALL IDENTICAL (1,700 runs), LEVELS 0-9 AND TOOLS OK, FAILURES OK,
FILES OK, USAGE ERRORS OK, ROUND TRIP OK, NO-BGZF BUILD OK, OUT OK, exit 0.

### Round 3 (decisions 11, 12)

Claude accepts; GPT found two cases, each with a second injected failure:
11. **The duplicate's `close` is checked.** If it fails, "cannot write <path>", exit 2 (it was
    ignored: exit 0). With no descriptor left, a written end-of-file block then stays.
12. **The take-back is exact unless it fails itself.** If the `ftruncate` through the duplicate
    fails, or the duplicate's own `close` fails after it, the error is reported (exit 2) and the
    file may keep its end-of-file block. Law machine's comment, `io64.c` and `docs/LAWS.md` say so
    in one clause.

Tests (`test/out.sh`): the close shim can fail only the n-th close of the path
(`FB_CLOSEFAIL_NTH=2`: the file's close succeeds, the duplicate's fails), for BGZF and for plain
output: exit 2, "cannot write", the file complete; and it can fail the take-back's `ftruncate`
(`FB_TRUNCFAIL`, only for a length above 0, so the open's emptying still works): exit 2, the file
keeps the end-of-file block. GPT's `finalization.py` could not be run here (its `final_fault.so`
is not in `/tmp/fb-review8-r3`); the two tests cover the same cases.

Checks: the gate through `test/bcheck.sh` (17 TODOs in `examples.bend`, 88 unsafe or foreign defs
in `main.bend`, ALL PROOFS CHECK with `--check-only` and `--verdict`); `test/out.sh` in full on the
normal build with `NOLIB=`: ALL IDENTICAL (1,700 runs), LEVELS 0-9 AND TOOLS OK, FAILURES OK,
FILES OK, USAGE ERRORS OK, ROUND TRIP OK, NO-BGZF BUILD OK, OUT OK, exit 0.
