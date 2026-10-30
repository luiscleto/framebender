# Index output: `-W` (phase J)

Brief: `notes/briefs/INDEX.md`. Branch `index`.

## Status

- **Step 1 (design and draft): the law review is closed** after round 3. Decisions 25–27 (driver
  text and code) are applied.
- **Step 2 (the implementation) is done:** "Step 2" below. Driver review 9's decisions 1–6 are
  applied ("Driver review 9" below); it waits for round 2 of the driver review.
  - The reviews: `reviews/{claude,gpt,grok}-index-law.md` and `-r2.md` in the main checkout
    (round 2: Grok ACCEPT, Claude and GPT should-fix only; round 3: GPT ACCEPT, Claude and Grok
    one should-fix each).
  - The lead's decisions 1–27: `reviews/responses-index-law.md`.
  - What changed for each decision: "Round 3", "Round 2" and "Round 1" below.
  - One thing outside the repository: htslib 1.24 without libcurl is installed at
    `~/.local/opt/htslib-1.24-nocurl` (decision 23).
- **The law draft is applied to a scratch copy**, `data/tmp/index/draft`, with the diffs in
  `data/tmp/index/{types,machine,examples,build}.diff` and the new `draft/tools/build_htslib.sh`.
  They are copied in full below.
  - `examples.bend` was checked there through `test/bcheck.sh` (`--check-only`): 19 TODOs
    (the 17 of today's gate, plus the new laws `index` and `index_sink`) and no errors. All 32
    new examples hold.
  - Three false examples were refused, one error each. They sit in `ex_false.bend`,
    `ex_false2.bend` and `ex_false3.bend`, since the checker reports only a file's first error:
    - `-W -Oz` to stdout is indexed at `-.csi`;
    - `-W=bai` is an index option;
    - `-W` changes the route (here, the `-o` path).
- **A scratch prototype of the driver** (`data/tmp/index/proto/`, binary `data/tmp/index/fbp3`,
  built by the draft `build.sh`) builds the index on the fly, with round 3's open order. Its
  index is byte-identical to `bcftools index` (CSI) and `tabix -p vcf` (TBI) of the same
  file on every input tried, at 1, 3 and 16 threads, levels 6 and 0. Its output, stdout, stderr and exit code
  are those of the same run without `-W`.
- **Whole genome, `-c w -Oz`:**
  - framebender alone: 2.85–3.03 s (step 1), 2.87–3.03 s (round 1);
  - with the on-the-fly index: 3.33–3.41 s with round 1's prototype (`bench6.txt`), 3.26–3.42 s with step 1's;
  - `bcftools norm -Oz -W --threads 16`: 6.38–6.62 s (step 1).

## Driver review 9

Reports `reviews/{claude,gpt,grok}-driver9.md` in the main checkout and the lead's decisions 1–6
in `reviews/responses-driver9.md`. There was no blocker, and every finding was in the trusted
driver, its comment or its tests. The laws are unchanged.

1. **CSI needs `##fileformat=VCF` first** (`io64.c`). The writer keeps the text's first 16 bytes
   (`head`, `nhead`, filled block by block in `idx_block`). For CSI, once there are 16 that are
   not `##fileformat=VCF`, the index's error flag is set. `idx_finish` also sets it for a text
   shorter than 16 bytes. The run then ends as any "cannot index" does: exit 2, no end-of-file
   block, no index. That is what `bcftools index` does, because htslib's `hts_detect_format`
   reads the format from those bytes (`hts.c:687`). TBI is unchanged, since `tabix -p vcf`
   accepts such a file. The cost is one comparison per run, off the per-line path.
2. **An older `<stem>.csi` hides a new `.tbi`** (`io64.c`'s `idx_check_hidden` at step 3; code
   2012; `main.bend`'s `ix_msg`, `ix_stem`, `ix_cut`). htslib 1.24's local search order is
   `hts_idx_check_local`'s, which `idx_find_and_load` uses for every local index load:
   - `f.csi`;
   - `<stem>.csi`;
   - for a TBI load, `f.tbi`, then `<stem>.tbi`.

   `<stem>` is `f` cut at its last `.` after the first byte, even inside a directory name. The
   first name `stat` finds is read. `f.csi` and `f.tbi` are the names step 5 moves aside, and a
   CSI comes first, so the only name that can hide ours is `<stem>.csi` before a TBI. While it
   exists, the run is refused with nothing changed: `error: cannot write o.vcf.gz.tbi (htslib
   would read o.vcf.csi first)`. The file is left alone. This is stated in law machine's comment
   (step 3 and the list of errors), the README, `docs/LAWS.md` and "The files" above. One case
   follows from htslib's rule: with `-o x.csi -Oz -Wtbi`, `<stem>.csi` is the `-o` file itself,
   so the run is always refused.
3. **An index name that is a symlink to a directory** (`idx_check_name`): `stat` is now checked
   too, and a name that resolves to a directory is refused ("cannot write <name>") before
   anything is moved or emptied.
4. **"Byte for byte" needs libdeflate:** law machine's comment now says "byte for byte when
   their htslib compresses as the linked one does (libdeflate), else the same index once
   decompressed". The same goes for the README, `docs/LAWS.md` and `NOTES.md`.
5. **The reference is "the same file under a `.vcf.gz` name"**, since tabix takes a `.cram` name
   down its CRAM path: the same files.
6. **Tests:**
   - `test/index.sh` runs each case once with CSI and once with TBI, choosing the format
     explicitly. Each format rotates its own spellings: five for CSI, three for TBI.
   - `test/gen_index.py` adds three inputs:
     - `noff.vcf`: no `##fileformat` line;
     - `cfirst.vcf`: a `#` line before `##fileformat`;
     - `biglen.vcf`: two `##contig` lines of 70 KB, with lengths past 2^32 before and after the
       padding, so they set CSI's levels across a block boundary.
   - The new file cases:
     - the `-o` file hard-linked to `.tbi`;
     - stderr appending to `.tbi`;
     - GPT's case: the `-o` path through `.csi`, a symlink to a directory;
     - `.tbi` as a symlink to a directory;
     - an older `o.vcf.csi`, shown first to break `tabix -l`, then with `-Wtbi` (refused, file
       left), with `-W` (runs), and as a dangling symlink (runs);
     - `d.csi` for `-o d.x/out`;
     - `-o x.csi -Wtbi`;
     - an existing `.csi.old`: the moved index goes to `.old1`, left there when its removal is
       made to fail; the `.old` itself is never touched.

   On the previous binary (`fbw2`), the directory-symlink and `<stem>.csi` cases fail
   (exit 0). The differential rule catches finding 1 on `noff` and `cfirst`.

Files changed: `io64.c`, `main.bend` (the 2012 message, which must name `<stem>.csi`),
`MACHINE.bend` (comment only), `README.md`, `docs/LAWS.md`, `docs/DEVELOPMENT.md`, `NOTES.md`,
`test/index.sh`, `test/gen_index.py` and this note.

**Results** (binary `data/tmp/index/fbw3`, plus `fbw3_nohts`, `fbw3_plain` and the rebuilt
small-piece builds; `build_r4.sh`, `check_r4.sh`, `tests_r4.sh`):
- **check.sh, through `test/bcheck.sh`:**
  - `PROOF.bend --check-only` and `--verdict`: ALL PROOFS CHECK;
  - `examples.bend`: 19 TODOs, no errors;
  - `main.bend`: the "rely on unsafe" list, now with `ix_stem` and `ix_cut`.
- **`test/index.sh` with `PIECES`** (`t4_index.txt`): 840 `-W` runs follow the per-format rule,
  and every other section passes (queries, injection with 50 runs, files, builds, usage, threads).
  36 case-and-format pairs are refused by the tool and give "cannot index". With both formats
  run on every case, the list now also has the TBI of `e2_posbig`, `len41`, `rw_crlf` and
  `rw_multi`, which the old rotation never ran; it also has `noff` and `cfirst` for CSI only, and
  `biglen` for TBI only (positions past 2^29). `biglen`'s CSI is `bcftools index`'s, byte for
  byte.
- **`test/index.sh` with `BIG=1`** (`t4_index_big.txt`): 438 runs, ALL PASS.
- **`test/out.sh`** (`t4_out.txt`, `NOLIB` the plain build): 1,700 identical, every section OK.
- **No timing:** the hot path gains one 16-byte comparison per run (in `idx_block` until 16 bytes
  are seen) and one `stat` per name at the open.

## Step 2: the implementation (for the driver review)

The accepted draft is applied to the tracked files, the laws are proven, and the driver is
written from the prototype. Not committed: the lead commits on `index`.

**Tracked changes:**
- **Science layer and contract** (the draft as reviewed, `data/tmp/index/*.diff` above):
  `types.bend`, `MACHINE.bend`, `examples.bend`.
- **Proofs:**
  - `proof_f_args.bend`: `w8` is the `-W` pick, `w9` the VCF-path fallback, one more pick in
    each of the four walks, `idx_inv`, and the `Drv` patterns;
  - `proof_f_index.bend` (new, about 620 lines):
    - `wfmt_none` and `idx_step`: the eight words, by cases;
    - `idx_un`, `parse_idx`, `index`;
    - `unidx` with its walk (`ui_step`, `ui_go`, `sink_same`, `thr_same`), then `index_sink`;
    - `index_ok`;
  - `PROOF.bend` forwards `M.index` and `M.index_sink`.
- **Driver:**
  - `io64.c`: the prototype's writer, inlined under `FB_HTSLIB` with `FB_LIBDEFLATE`. The new
    effect `Io.out_index` replaces the environment variable, and error codes 2003–2011 replace
    the prototype's own messages;
  - `main.bend`: `B.Args.index`, `BadIdx` in `main.k`, `Io.out_index` after `Io.out_set`,
    `ix_msg`;
  - `io64.js`: `Io.out_index` answers 2003;
  - `build.sh` and `tools/build_htslib.sh` (new), as drafted.
- **Tests:** `test/index.sh`, `test/gen_index.py` and `test/fi_shim.c` (all new).
- **Docs:** `docs/LAWS.md` (laws `index` and `index_sink`, the trusted index writer), the README
  (install, `-W`, the differences, the timings), `docs/DEVELOPMENT.md` (the htslib build,
  `test/index.sh`) and `NOTES.md` (phase J).

**check.sh, through `test/bcheck.sh`** (4 GB cap):
- `PROOF.bend --check-only`: ALL PROOFS CHECK;
- `PROOF.bend --verdict`: ALL PROOFS CHECK;
- `examples.bend`: 19 TODOs (the laws it imports), no errors;
- `main.bend`: the expected "rely on unsafe" list.

**Tests** (binary `data/tmp/index/fbw2`, built by `build.sh` against
`~/.local/opt/htslib-1.24-nocurl`):
- **`test/index.sh`:**
  - **with the small-piece builds** (`PIECES`: 300, 1,000 and 70,001 bytes): 810 `-W` runs all
    follow the per-format rule (`t_index.txt`). Twenty-six case-and-format pairs are refused by
    the tool, and each gives "cannot index". Some come from the generated corpus (`rw_cr`,
    `rw_crlf`, `rw_mix`, `rw_multi`, `e2_posbig`);
  - **with `BIG=1`** (the 1000 Genomes slice and its chr22, the whole genome): 426 runs
    (`t_index_big.txt`);
  - **the other sections pass:** queries (9 regions at block and 16 kb bin boundaries), failure
    injection (50 runs: each step and index name, CSI and TBI, the `link` fallback), files, the
    builds (`NOHTS`, `PLAIN`, `build.sh`'s refusals, `build_htslib.sh`'s checksum), usage errors,
    and the threads seen with each spelling.
- **The existing scripts** (`t_existing.txt`), against the base commit's build
  `data/tmp/index/fb`, which is the main checkout's binary:
  - `same.sh`: 128 identical runs, on `fbw2` and on each small-piece build;
  - `par.sh`: 312 identical runs, the same;
  - `out.sh`: 1,700 identical, and every section OK, `NOLIB` included;
  - `threads.sh`: 2,128 identical.

  `same.sh`'s default reference `data/tmp/fb_ref` is a build of Oct 28 and differs from today's
  main on `chromchange` (both under `-c e` and `-c w`). That difference predates phase J, so the
  scripts ran against `fb`.

**Timing** (`bench7.txt`: under the bench lock, `nice -n 19`, `timeout`, CPUs 0–15,
interleaved; `-c w`; chr22 5 rounds, whole genome 3):

| | chr22 | whole genome | peak memory (whole) |
|---|---|---|---|
| bcftools `-Oz --threads 16` | 0.12–0.13 s | 6.11–6.56 s | 17 MB |
| bcftools `-Oz -W --threads 16` | 0.13–0.14 s | 6.52–6.58 s | 30–31 MB |
| framebender `-Oz` | 0.07–0.08 s | 2.99–3.29 s | 344–350 MB |
| framebender `-Oz -W` | 0.09–0.10 s | 3.43–3.61 s | 359–360 MB |
| framebender `-Oz -Wtbi` | 0.09 s | 3.28–3.50 s | 359–361 MB |
| framebender `-Oz1 -W` | 0.08–0.09 s | 2.52–2.60 s | 358–362 MB |

- **Against bcftools:** `-Oz -W` is 1.8–1.9× faster on the whole genome, 1.3–1.6× on chr22.
- **By `--threads`:** whole genome `-Oz -W` takes 16.35 s at 1, 5.28 s at 4, 3.80 s at 8 and
  3.76 s at 32 (62, 141, 221 and 637 MB).

## Round 3

The law review is closed: laws `index` and `index_sink` and the parser are accepted by all
three. Decisions 25–27 (`reviews/responses-index-law.md`) are driver text and code, for the
driver review. The checks are in `data/tmp/index/r3_fi.txt`, on the round 3 prototype `fbp3`.

25. **A failed move back leaves `<name>.old`.** One clause in each place: law machine's comment,
    the prototype's comment (`idx_unstage`, `idx_move`) and "The files" below. The index whose
    move back fails stays as `<name>.old` beside the unchanged `-o` file. The message stays the
    step's own ("cannot write <name>" or "cannot write <path>"). The step 5 row is now in the
    injection table, for both formats:
    - CSI: moving `.tbi` aside fails, then moving `.csi` back fails;
    - TBI: moving `.csi` aside fails, then moving `.tbi` back fails.

    In each, the message names the second index, the `-o` file is old, the first index is left as
    `.old`, and the second is unchanged.
26. **The `link` and `unlink` fallback.** When `renameat2` answers EINVAL, ENOSYS or EOPNOTSUPP,
    a move is `link(name, t)` then `unlink(name)`:
    - `link` never replaces a file: EEXIST keeps the `.old1`, `.old2` loop;
    - if the unlink fails, `t` is removed and the move fails, with nothing changed;
    - where `link` fails too, the move fails as before: no check-then-rename;
    - the moves back use the same function.

    Linux only; macOS (`renamex_np`) is a later port. Checked by injection: every `renameat2`
    answers the errno, for both formats.

    | case | exit | result |
    |---|---|---|
    | EINVAL, ENOSYS, EOPNOTSUPP | 0 | complete output, new index, the other removed, nothing left |
    | EINVAL, and `link` refused (EPERM) | 2 | "cannot write o.vcf.gz.csi", nothing changed |
    | EINVAL, `link` of the second index fails | 2 | "cannot write" (that index), the first moved back, nothing changed |
    | EINVAL, `unlink(name)` after the link fails | 2 | "cannot write o.vcf.gz.csi", the link removed, nothing changed |
    | EINVAL, then `ftruncate` fails | 2 | "cannot write o.vcf.gz", both moved back (by the fallback), nothing changed |
    | EINVAL, a stray `.csi.old` there | 0 | `.old1` used and removed; the stray left alone |

    All of round 2's rows still hold: 52 rows in all (`r3_fi.txt`).
27. **`tools/build_htslib.sh`:**
    - downloads with `curl --proto '=https' --tlsv1.2`;
    - checks the SHA-256 with `sha256sum`, or `shasum -a 256` where that is missing;
    - checked: a wrong tarball is refused, with nothing installed.

## Round 2

Decisions 20–24 (`reviews/responses-index-law.md`), and what was done for each. The checks are
in `data/tmp/index/r2_*.txt`, run on the round 2 prototype `fbp2`.

20. **The old indexes are renamed aside before the `-o` file is emptied** (GPT's order). The open
    is now:
    1. open without emptying, `O_NONBLOCK`;
    2. `fstat`: a regular file, not an input;
    3. `lstat` both index names;
    4. create the temporary file;
    5. rename each old index that exists to `<name>.old` (`.old1`, ... on EEXIST: `renameat2`
       with `RENAME_NOREPLACE`, so nothing is replaced). If the second one fails, the first is
       moved back;
    6. `ftruncate`; if it fails, both are moved back;
    7. unlink the moved names.

    A failure in steps 1–6 changes nothing (but see decision 25: a failed move back). A failure
    in step 7 leaves `<name>.old`, a file htslib
    never reads, and the run goes on with no message. The prototype, law machine's comment and
    "The files" say this.

    **Checked by failure injection** (`r2_fi.sh`, an `LD_PRELOAD` shim, `r2/fi_shim.c`, that
    fails one chosen libc call by path). Each step and each index name was injected, with the
    index written as CSI and as TBI. Each run starts from an old `-o` file and two old indexes
    with their own bytes:

    | step injected | exit | message | `-o` | the index written | the other name | left behind |
    |---|---|---|---|---|---|---|
    | none | 0 | | complete | new (= the tool's) | removed | nothing |
    | 1 open `-o` | 2 | cannot write o.vcf.gz | old | old | old | nothing |
    | 2 `fstat` `-o` | 2 | cannot write o.vcf.gz | old | old | old | nothing |
    | 3 `lstat` `.csi` / `.tbi` | 2 | cannot write o.vcf.gz.csi / .tbi | old | old | old | nothing |
    | 4 the temporary file | 2 | cannot write <the index> | old | old | old | nothing |
    | 5 rename `.csi` / `.tbi` aside (EACCES; also EPERM, the sticky case) | 2 | cannot write o.vcf.gz.csi / .tbi | old | old | old | nothing |
    | 6 `ftruncate` | 2 | cannot write o.vcf.gz | old | old | old | nothing |
    | 6 `ftruncate`, and moving `.csi` back fails too | 2 | cannot write o.vcf.gz | old | `.csi` is gone | old | `o.vcf.gz.csi.old` |
    | 7 unlink `.csi.old` / `.tbi.old` | 0 | | complete | new | removed | that `.old` file |
    | end: close `-o` (phase H) | 2 | cannot write o.vcf.gz | no EOF block | none | none | nothing |
    | end: save to the temporary file | 2 | cannot write <the index> | no EOF block (taken back) | none | none | nothing |
    | end: rename into place | 2 | cannot write <the index> | no EOF block (taken back) | none | none | nothing |
    | end: close of the duplicate | 2 | cannot write o.vcf.gz | complete | none (removed) | none | nothing |

    The same rows hold for `-W` and `-Wtbi`. The double fault (`ftruncate`, then a failed move
    back) is the one case with an old index stranded: the `-o` file is unchanged and has only lost
    its index, which is a reason to re-index, never a wrong answer. Earlier rounds' T4 cases
    (`r2_cases.txt`) still pass.
21. **Bend's runtime stops with `_exit`,** so `atexit` does not run. The wording is now "no run
    leaves the temporary file unless it is killed or Bend's runtime stops it", in law machine's
    comment, `idx_proto.h` and "The files".
    - Checked: chr22 with a last record at POS 3·10^14, past 2^48. It gives "bend: a Nat past the
      largest immediate 2^48-1", exit 1, and leaves `o.vcf.gz.csi.tmp`, no index (the old `.csi`
      already removed at the open).
    - The test plan expects exactly that.
22. **The differential oracle is per format.**
    1. The run without `-W` comes first. If its code is not 0, each `-W` run must be that run
       exactly, with no index.
    2. Otherwise CSI is judged by `bcftools index` and TBI by `tabix -p vcf`, each on its own.

    Checked (`r2_oracle.sh`, at `--threads` 1 and 16, CSI and TBI, `-c e`):

    | case | CSI | TBI |
    |---|---|---|
    | `small` | = `bcftools index` | = `tabix` |
    | POS 600,000,000 (out of scope, passed) | = `bcftools index` | refused: cannot index |
    | INFO/END 600,000,000 | = `bcftools index` | refused: cannot index |
    | POS 5·10^9, with `##contig` lengths (6 levels) | refused: cannot index | refused: cannot index |
    | POS 5·10^9, no lengths (8 levels) | = `bcftools index` | refused: cannot index |
    | POS 3·10^11, no lengths | refused: cannot index | refused: cannot index |
    | a leading-zero POS | refused: cannot index | refused: cannot index |
    | the same, then a `-c e` stop (code 1) | the run without `-W`, no index | the run without `-W`, no index |

    A refusal of CSI alone cannot happen at `min_shift` 14: CSI's levels never hold less than
    2^32, and TBI holds 2^29. The test plan says so.
23. **htslib without libcurl:**
    - installed at `~/.local/opt/htslib-1.24-nocurl` by the new
      `tools/build_htslib.sh [PREFIX] [TARBALL]`, drafted in `draft/tools/`. It checks the
      release tarball's SHA-256 and configures `--disable-libcurl --disable-gcs --disable-s3
      --with-libdeflate`. It was run here with the tarball already in `src/`;
    - **the draft `build.sh`** finds it with `pkg-config` (`PKG_CONFIG_PATH`, by default that
      prefix's). Before `bend` runs, it refuses:
      - no htslib 1.24;
      - a `libhts.a` whose `static_libs` name `-lcurl`;
      - a `libhts.a` without the two functions.

      The message names the prefix, the script and the three `--disable-*` flags.
    - `FB_NO_HTSLIB=1` builds without htslib.
    - Checked: `PKG_CONFIG_PATH` at the libcurl build is refused, an empty one too, and no binary
      is written. The default builds `fbp2` (5.72 MB, 8 shared objects). `FB_NO_HTSLIB=1` builds
      a 1.78 MB binary with no htslib.
    - The prototype is now built by the draft `build.sh` itself (`build_proto.sh` only swaps in
      the prototype's `io64.c`).
24. **The usage line** is cut to one short clause: `  -W also removes FILE's old .csi/.tbi`
    (38 columns). The full explanation, including what a run without `-W` leaves, goes in the
    README (step 2).

Re-run on `fbp2`, all as in round 1:
- **identity** (`r2_ident.txt`): the 48 runs, all CSI and TBI identical, outputs and messages
  as without `-W`, no temporary file;
- **the round 1 cases** (`r2_cases.txt`): T1–T6;
- **the draft** (`check_examples.txt`): 19 TODOs, no errors.

No timing was needed. The open gains two renames and no work per line.

## Round 1

Kept as written for round 2; decisions 20, 21 and 24 above replace parts of 2, 9 and 15.

Every decision of `reviews/responses-index-law.md`, and what was done for it. "Checked" means a
run of the prototype (`data/tmp/index/r1_*.txt`, `bench5.txt`) or of the draft (`bcheck.sh`).

1. **The `reported` static in `tbx_parse1` (a data race).** Fixed in the prototype:
   - a line holding `END=` anywhere is parsed under a mutex. That is a superset of htslib's own
     test, which looks for `END=` in INFO.
   - Every other line is parsed without a lock.
   - The `io64.c` comment (`idx_proto.h` in the prototype) says why.

   **The timing (`bench6.txt`).** The plan was the whole genome with `END=` on every record.
   framebender alone took 419 s on that file (`bench5.txt`), so I stopped it: its own INFO/END
   check is slow (a lead below). The lock was timed instead on chr22 with `END=` on every record
   (`h22`) and with `END=1` on every 50th (`g22`), 5 rounds, interleaved, under the bench lock,
   and on the whole genome as it is, 3 rounds:

   | input | no index | `-W`, lock | `-W`, no test, no lock |
   |---|---|---|---|
   | `h22` | 1.07–1.10 s | 1.11–1.23 s | 1.09–1.20 s |
   | `g22` | 4.36–4.40 s | 4.41–4.45 s | 4.42–4.49 s |
   | whole genome | 2.87–3.03 s | 3.33–3.41 s | 3.27–3.43 s |

   The ranges with and without the lock overlap on every input: its cost is within the noise.

   **The lead, outside phase J:** framebender's INFO/END check is slow.
   - chr22 takes 93 ms as it is, 1.19 s with a valid `END=` on every record, and 4.6 s when 2% of
     them are below POS (passed with a problem);
   - this is today's binary (`data/tmp/index/fb`), without `-W`;
   - gVCF-like input would meet it.
2. **The order at the open.** Written once, in law machine's comment and in "The files" below,
   and implemented in the prototype:
   1. open without truncating, `O_WRONLY | O_NONBLOCK`;
   2. `fstat`: a regular file, not an input;
   3. `lstat` both index names: refuse if either is a directory, cannot be looked at, or is
      (itself, or the file a symlink there names, through `stat`) the output, an input or
      stderr's file;
   4. create the temporary file;
   5. `ftruncate`;
   6. unlink both old indexes.

   A failure in (1)–(5) leaves the old file and both old indexes. Checked (`r1_cases.txt`, T4):
   - `-o` a symlink to its own `.csi`: refused, both unchanged;
   - `.tbi` a directory next to a real `.csi`: refused, nothing changed;
   - a read-only `-o` in a writable directory: refused, nothing changed;
   - a missing FASTA (a failure before the open): nothing changed;
   - `.tbi` a symlink to the VCF, and `.csi` a hard link to it: "output is an input", nothing
     changed;
   - success with both old indexes present: the new one is `tabix`'s, the other is removed.

   New message: "cannot write <path>.csi (it is the -o file)", when the `-o` path names an index
   through a symlink or a hard link.
3. **A FIFO `-o`.** Opened with `O_NONBLOCK`; ENXIO is "not a regular file". Checked under a 20 s
   timeout (T3):
   - with no reader, exit 2 in 25 ms;
   - with a reader, the same message, and the reader gets 0 bytes;
   - `-o /dev/null`: the same message, and `/dev/null.csi` is not created.
4. **Index errors have their own flag** (`io64_ix.bad`), never `io64_out.err`. At `Io.out_close(c)`:
   - for c ≠ 0, the flag is ignored and no index is written: the run is the run without `-W`;
   - for c = 0 with the flag set, "cannot index <path>" comes after all of the machine's
     messages, with no end-of-file block, exit 2.

   Checked (T5) at `--threads` 1, 16 and 128:
   - **an unindexable line under `-c e`** (a leading-zero POS on an out-of-scope record): stderr is
     that of the run without `-W`, then the new line. The data is the same less the end-of-file
     block, and there is no index. `tabix -p vcf` refuses the same text (exit 1).
   - **the same file with a `-c e` stop further on:** stdout, stderr, exit code (1) and output
     bytes are those of the run without `-W`. There is no index, and the old indexes were
     removed.
5. **Law `index_sink`**, new in `MACHINE.bend`. Under `he` and `hx`, `route(command(pre, x <>
   post)) == route(command(pre, post))`, where `route(argv)` is `Route{B.Args.output(argv),
   B.Args.threads(argv)}`.
   - It needs only `he` and `hx`, not law `index`'s other premises, so it is stated with those
     two. That makes it the stronger law.
   - `B.Args.index` is now computed from `Args.sink`'s `Sink` (`B.Args.idx.mk(Drv.idx(t),
     Args.sink(t))`), so the index and the output agree by definition.
   - New examples: `idx_mk_*` and `route_*`. A false `route` example is refused.
6. **"cannot index" is stated by reference:** exactly when `tabix -p vcf` (TBI) or `bcftools
   index` (CSI) refuses the same file. The known causes follow, and "never" is gone (law
   machine's comment, "When the index fails" below). The tests Claude listed are in the test
   plan.
   - A finding from the checks: framebender rewrites a leading-zero POS on a record it judges
     (`chr22 015884846 … C G` comes out as `15884846`, counted as changed). The leading zero
     stays only on lines it passes unchanged (out of scope, or `-c w`'s problem lines), and only
     there does "cannot index" arise.
7. **Index names that look like URLs.** htslib is given `./` before a relative path. Checked
   (T2), CSI and TBI each: `-o file:x.vcf.gz`, `data:x.vcf.gz`, `mem:x.vcf.gz`,
   `chr1:1-1000.vcf.gz` and `http:/x.vcf.gz` (with a directory `http:`).
   - Each writes exactly the two local files.
   - The index equals `bcftools index` / `tabix` of a copy.
8. **Indexing before the frees.** The prototype already did this: `io64_wrun` calls `idx_block`
   before it frees `j->own` and before it counts the block written. `Io.out_write` frees the
   machine's buffer only after `io64_out_drain`. The carried tail is copied inside `idx_block`.
   The last short blocks (`io64_out_tail`) are copies, indexed the same way. All of this is now
   said in the comment.
   - An empty line was never a NULL dereference: `kputsn` allocates even for 0 bytes. It is a
     line `tbx_parse1` refuses, so it gives "cannot index". The allocation itself is now
     checked (decision 13).
9. **The temporary file is created at the open** (step 4 of decision 2):
   - its name is `<index>.tmp`; on EEXIST the prototype tries `.tmp1`, `.tmp2`, ...;
   - it is removed on every failure path, and by an `atexit` handler for a run that dies in the
     driver or the runtime.

   Checked:
   - T4 h: a stray `.tbi.tmp` is left alone, `.tmp1` is used, and the index is right;
   - T6: a cut BGZF input after the open ("bad BGZF", exit 2) leaves no temporary file and no
     index.
10. **The error order:**
    1. `BadIdx` in `main`, before any input is opened;
    2. "no BGZF in this build" for any BGZF output;
    3. "no index in this build" only when BGZF works and htslib does not.

    Written in law machine's comment and in the test plan. The libdeflate-only binary is built
    by `build.sh` with `FB_NO_HTSLIB=1`. The plain `bend` binary is no longer said to print "no
    index".
11. **The empty index.** As `tbx_index`: no records means `hts_idx_init` with the first settings,
    and no level adjustment. Checked (T1): a header-only output without `##contig` lengths.
    - The old prototype's CSI differs (8 levels).
    - The round 1 prototype matches `bcftools index`.
    - With lengths, both match, since the levels stay at 6 for chr1's length.
12. **`io64_threads_of`** recognizes the eight words (`io64_wfmt`). Checked with a harness on
    the prototype's own functions (`r1_threads.sh`):
    - each spelling at five positions keeps `--threads 7`;
    - `-o -W` is a path;
    - `-W tbi in.vcf` (two VCF paths) and `-Wbai` give no thread count, as the parser refuses
      them.
13. **The prototype's allocations:**
    - every `malloc`, `realloc`, `kputsn`, `kh_put` and the metadata copy is checked, and a
      failure is "cannot index";
    - `ss`, `sl`, `beg` and `end` are set for every line, and CHROM's offset is moved only for
      records;
    - the metadata takes `ed_is_big()`'s swap, as `tbx_set_meta` does.
14. **The wording,** in the summary, law `index`'s comment and law machine's comment:
    - "changes nothing in the machine's report" (not "the program writes");
    - "a run that does not exit 0 leaves no index" is now scoped to "once the open reached step
      (6)";
    - "the file is complete exactly when the index is there" is now scoped to a normal exit, with
      phase H's take-back exceptions spelt out;
    - `docs/LAWS.md` will say the process can exit 2 where the machine's code is 0.
15. **A rewrite without `-W` leaves `<out>.csi`.** Not in phase J. The draft's usage message
    gains a second line saying so (below). The README's Run section will say it in step 2.
    Recorded as an open lead in "Questions".
16. **The two end cases** (a last line without LF pushed at the end-of-file block's address, and
    `hts_idx_finish` at that same address) are written in the driver section, the prototype's
    comment and law machine's comment.
17. **htslib without libcurl:**
    - the prototype links a `libhts.a` built `--disable-libcurl --disable-gcs --disable-s3`
      (`data/tmp/index/hts-nocurl`, `build_hts.sh`);
    - its `static_libs` are `-lpthread -lz -lm -lbz2 -llzma -ldeflate`;
    - the binary is 5.72 MB (6.06 MB before) and loads 8 shared objects instead of 30;
    - `build_proto.sh` checks with `nm` that `libhts.a` defines `tbx_parse1` and
      `hts_adjust_csi_settings`, and that `pkg-config` says 1.24;
    - `idx_proto.h` stops on `HTS_VERSION != 102400` and has a `_Static_assert` on
      `tbx_intv_t`'s offsets and size.
18. **The test oracles.** All fixed in the test plan:
    - EOF block by its 28 bytes, not `bgzip -t`;
    - MALFORMED POS and blank lines stop with exit 1 even under `-c w`, so they are not
      "cannot index" cases;
    - the real exit codes;
    - the differential rule over the whole corpus;
    - the boundary cases, NUL in a line, stderr across `--threads`, injected failures, region
      queries at boundaries;
    - `-W -o x.vcf.bgz`, `x.VCF.GZ` and `--write-index tbi` (new examples);
    - the decision 2 order (already run on the prototype).
19. **"The eight documented forms"**, in the summary, the options and `Args.wfmt`'s comment. The
    note now says bcftools also takes `--write-index==tbi` and abbreviations.

Re-run for round 1:
- **Identity** (`r1_ident.txt`, 48 runs). Inputs: header-only, `END=` on every line, a record of
  200 KB, a header longer than a block, no final LF, `small`, chr22 and the scrambled file. Each
  ran at `-Oz` and `-Oz0`, `--threads` 1, 3 and 16, with CSI and TBI. All CSI and TBI are
  identical to the reference tools, the outputs and messages equal the runs without `-W`, and
  no temporary file is left.
- **Large inputs** (`bench5.txt`, under the bench lock): the 1000 Genomes slice (`-Oz` at
  `--threads` 16 and 3, `-Oz0` at 16), the 1000 Genomes chr22 (`data/kg/chr22.vcf.gz`, records
  of 14 KB) and the whole genome (`-Oz`, 16). CSI and TBI are identical to the reference tools'
  for each, and the CSI and TBI runs wrote the same output.
- **The new confirmed cases:** the empty CSI (T1), the `file:` path (T2), and a FIFO with no reader
  under a timeout (T3), as above.

## Summary

- **The option.** `-W` writes the output's index next to it, as `bcftools norm -W` does.
  - One word, in the eight forms bcftools documents: `-W`, `-Wcsi`, `-W=csi`,
    `--write-index`, `--write-index=csi` (CSI, the default), and `-Wtbi`, `-W=tbi`,
    `--write-index=tbi` (TBI).
  - The last one counts.
  - The index is `<-o path>.csi` or `.tbi`.
  - It needs BGZF output to a regular file named by `-o`. Otherwise the driver refuses the run:
    stdout or plain output before any input is opened, a FIFO or device at the open.
- **The header does not record it**, like `-o`, `-O` and `--threads`.
- **The laws.**
  - **A new law `index`,** in the style of `law threads`: adding one index option where an option
    is expected changes nothing in the machine's report (output bytes, messages, exit code).
  - **A new law `index_sink`:** it changes neither `B.Args.output` nor `B.Args.threads`.
  - **`B.Args.index`** says where the index goes, or that it cannot be written. It is built on
    `B.Args.output`'s `Sink`. `index_ok` is `output_ok`'s counterpart.
  - Law `output` and `B.Args.out_opt` do not change.
- **The driver** builds the index while it writes the BGZF blocks, with htslib's own code:
  - each compressor thread parses its block's lines with `tbx_parse1`, the parser `tabix` uses
    (lines with `END=` under a lock);
  - the writer thread pushes them in order with `hts_idx_push`, at the virtual offsets
    `bgzf_tell` would give a reader;
  - at exit 0 the index is finished and saved with `hts_idx_finish` and `hts_idx_save_as`.

  So the index is byte for byte what `tabix -p vcf` or `bcftools index` writes for the same file.
- **Files.**
  - At the open, every check comes before anything is changed. The temporary index file is
    created, and both old `<out>.csi` and `<out>.tbi` are renamed aside, before the `-o` file is
    emptied. They are removed only after it is emptied, so a failure at the open changes nothing.
  - The index is written only for exit 0, after the end-of-file block. It goes to the temporary
    file, which is then renamed into place.
  - Removing both old indexes matters because htslib reads `.csi` before `.tbi`: a stale `.csi`
    shadows a fresh `.tbi` silently (an experiment below shows 0 records returned instead of
    13,335). bcftools leaves stale indexes in place.
- **Cost:** +0.3–0.5 s on the whole genome (round 1: 3.33–3.41 s against 2.87–3.03 s) and +19 MB
  peak (step 1). The lead over bcftools is 1.9–2.0×.

## bcftools 1.24's behaviour

Checked on `bcftools norm` with scratch runs: `data/tmp/index/ex1.sh` to `ex3.sh` and `ex7.sh`.
The source of bcftools and htslib 1.24 is unpacked in `data/tmp/index/src`, read only.

**The option** (`vcfnorm.c`: getopt `W::`, `{"write-index", optional_argument}`;
`version.c: write_index_parse`):
- `-W`, `--write-index`, `-Wcsi`, `-W=csi` and `--write-index=csi` write `<out>.csi`.
- `-Wtbi`, `-W=tbi` and `--write-index=tbi` write `<out>.tbi`.
- These eight are the documented forms. `write_index_parse` also takes `=csi` and `=tbi` as the
  value, so `--write-index==tbi` works too. getopt also accepts abbreviated long options
  (`--write`).
- The value must be glued. With `-W tbi`, the word `tbi` is an input file: bcftools fails with
  "Failed to open file "tbi"".
- Any other value is refused with "Unsupported index format 'X'", exit 255. Examples: `-Wbai`,
  `--write-index=TBI` (the case matters).
- The last `-W` counts: `-W -W=tbi` writes `.tbi`, and `-W=tbi -W` writes `.csi`.

**The index's name** (`version.c: init_index2`): the `-o` path with `.csi` or `.tbi` appended,
whatever the path is (`-o o.gz -W` gives `o.gz.csi`). A path `out##idx##name` writes the output to
`out` and the index to `name`.

**When there is no index:**
- **Stdout** (no `-o`, or `-o -`, with any `-O`): "Error: failed to initialise index for -",
  exit 255, nothing written.
- **Plain output** (`-Ov -o o.vcf`, and `-Oz -o o.vcf`, where the extension wins):
  "[E::bcf_idx_init] Indexing is only supported on BGZF-compressed files", then "Error: failed to
  initialise index for o.vcf", exit 255. `o.vcf` is left behind, holding the header.
- **`-Ov -o o.vcf.gz -W`** is BGZF by the extension, so it is indexed.
- **A run that fails mid-file** (a REF mismatch with `-c e`): exit 255, `o.vcf.gz` left without an
  index. An index already at `o.vcf.gz.csi` is left as it was, now stale.
- **Unsorted output**: "[E::hts_idx_push] Unsorted positions on sequence #1: 16585810 followed by
  15221405", then "[flush_buffer] Error: cannot write to u.vcf.gz", exit 255, no index.

**The format:**
- **CSI:** `min_shift` 14 (`init_index2`). The levels start at `(31 - 14 + 2) / 3 = 6` and grow
  for longer contigs (`vcf_idx_init`, `hts_adjust_csi_settings`).
- **TBI:** `min_shift` 14, 5 levels. Positions past 2^29 do not fit.
- **The tabix metadata**, the 28-byte configuration and the contig names, is in both (`TBX_VCF`).

**The on-the-fly index is the index of the file.** On `small.vcf` and chr22, at `--threads` 0 and
4:
- `norm -W`'s CSI is byte-identical to `bcftools index` of the same file;
- `norm -W=tbi`'s TBI is byte-identical to `tabix -p vcf` of the same file;
- `bcftools index -t` gives the same bytes as `tabix -p vcf`, and `tabix -C` the same as
  `bcftools index`.

Both reference tools run htslib's `tbx_index` loop on the file (`tbx.c`), on a file named
`.vcf.gz` (tabix decides some formats by the name: a `.cram` name takes its CRAM path, even with
`-p vcf`). Before that, `bcftools index` detects the format: it refuses a file whose text does not
begin with the 16 bytes `##fileformat=VCF` (driver review 9, finding 1); `tabix -p vcf` does not
look. So the target "the same bytes as `bcftools index` / `tabix -p vcf` of our file" is also what
`bcftools norm -W` would write for our file. bcftools' own `.vcf.gz` is cut into different blocks, so its index differs,
as it should.

The index file is itself BGZF, compressed by htslib. So byte identity also needs the reference
tools' htslib to deflate as the linked one does. Here both are 1.24 with libdeflate, and the
no-libcurl build changes nothing there (`r1_ident.txt`).

**Order at the end** (`vcfnorm.c`): bcftools saves the index (`bcf_idx_save`), and then
`hts_close` writes the end-of-file block. The index is therefore older than the data, and htslib
warns when that is a whole second ("The index file is older than the data file").

**`tbx_index`, the loop the index must reproduce** (`tbx.c`, `bgzf.c`):
- **Lines** are those of `bgzf_getline`: split at LF, with one trailing CR removed. A last line
  without LF counts.
- **Meta lines.** A line whose first byte is `#` is skipped, wherever it is. The offset after it
  becomes the index's first offset (`hts_idx_init`'s `offset0`) if no record has come yet.
- **Contig lengths (CSI only).** Before the first record, the `##contig` lines' `length` values
  give the longest contig, which sets the levels (`adjust_max_ref_len_vcf`). Without any length,
  the levels follow from `min_shift` (8 for 14). A file with no record keeps the first settings
  (6 levels): its index is made after the loop, with no adjustment.
- **Each other line** is parsed by `tbx_parse1`:
  - CHROM;
  - POS read by `strtoll` in base 0, so `010` is octal 8 and `0x1A` is 26, minus 1. A value
    below 0 becomes 0, with a warning;
  - the end, from the REF length, a valid INFO/END (one that is not below POS: a smaller one is
    ignored with a warning, once per process, through a function-static `reported`), SVLEN for
    symbolic alleles, and FORMAT/LEN for `<*>` and `<NON_REF>`.

  A line it cannot parse (POS not a number, too few columns, an empty line) fails the whole index.
- **Contig ids** follow the order of first appearance (a hash of names). The names are saved in
  the metadata (`tbx_set_meta`).
- **Push.** Each record is pushed (`hts_idx_push`) at `bgzf_tell` after its line: the virtual
  offset where the line ends. A line that ends exactly at a block's end gets the next block's
  address and offset 0. So does a last line without LF: `bgzf_getline` moves past the block even
  without the delimiter. `hts_idx_push` refuses unsorted positions, a contig that comes back, and
  a position the index cannot hold.
- **Finish.** The index is finished at `bgzf_tell` after the end-of-file block is read: that
  block's address, offset 0.

**A stale `.csi` shadows a new `.tbi`** (`ex7.sh`):
1. `bcftools norm -W -o o.vcf.gz small.vcf`;
2. `bcftools norm -W=tbi -o o.vcf.gz chr22.vcf`, which leaves `o.vcf.gz.csi` from step 1;
3. `bcftools view -H -r chr22:20000000-30000000 o.vcf.gz` gives 0 records, without a warning,
   where the file has 13,335 there.

htslib looks for `.csi` before `.tbi` (`hts.c: idx_find_and_load`).

## The options

**`-W`, one word.** It is one of the eight documented forms:
- `-W`, `-Wcsi`, `-W=csi`, `--write-index`, `--write-index=csi`: CSI;
- `-Wtbi`, `-W=tbi`, `--write-index=tbi`: TBI.

The last one counts. Any other word that starts with `-W` or `--write` is refused as an unknown
option (a usage error), as it is today: for example `-Wbai`, `-W=TBI`, `-W=`, `--write` or
`--write-index==tbi`. A format in the next word is not read, as in bcftools. That word is then
an ordinary argument: `-W tbi` makes `tbi` the VCF path, or a usage error if there is one
already.

All eight words are usage errors today, so no command line accepted today changes meaning. As
values (`-f -W`, `-o --write-index`), they stay values.

**Where the index goes**, `B.Args.index(argv)`, built on the `Sink` that `B.Args.output(argv)`
gives (`B.Args.idx.mk`):
- **`NoIdx`:** no `-W`.
- **`Idx{fmt, path}`:** `-W` with a `Sink` that is BGZF to a file. `path` is that file's path
  followed by `.csi` or `.tbi`, as in bcftools. The spelling is kept: `x.VCF.GZ` gives
  `x.VCF.GZ.tbi`. "BGZF to a file" is exactly `Args.output`'s rule: the extension, else `-O`. So
  `-Ov -o o.vcf.gz -W` is indexed, as in bcftools.
- **`BadIdx`:** `-W` with stdout (no `-o`, or `-o -`) or with plain output. The driver stops before
  any input is opened: "error: -W needs a BGZF -o file", exit 2.

**Why `BadIdx` is not a usage error.** If `Args.parse` refused `-W` without a BGZF `-o`, whether a
line is accepted would depend on two options together. Then "adding `-W` changes nothing" would
be false as stated, and law `index` would need a premise on the whole line. Phase H made the same
choice for `-Oz -o x.vcf` (question 1 there). Keeping parse blind to `-W` keeps the law a plain
equality. The rule still lives in the reviewed layer (`Args.index`, pinned by examples), and the
message says what is wrong, where a usage error would not.

**The usage message** gains a short second line (decisions 15 and 24). The README says the rest:
a run without `-W` leaves an old index, which htslib warns about only when it is a second or more
older than the file.

```
usage: framebender norm -f ref.fa [-c e|w] [-w N] [--threads N] [-o FILE] [-O v|z|z0-9] [-W[=csi|tbi]] in.vcf
  -W also removes FILE's old .csi/.tbi
```

**Not taken from bcftools:**
- `##idx##` in the `-o` path: the path stays literal, as in phase H;
- abbreviated long options (`--write`), and `--write-index==tbi`;
- a BCF index (no BCF output);
- leaving stale indexes when `-W` is given;
- saving the index before the end-of-file block;
- exit 255: the errors here exit 2.

## The header

`-W` is **not** recorded in `##framebender_normCommand`, like `-o`, `-O` and `--threads`. The text
is the same with or without an index, and law `index` says so.

## The laws

**A new law `index` in `MACHINE.bend`**, stated as `law threads` is:
- wherever the parser expects an option (`B.Args.expecting(pre)`), adding one index option `x`
  (`B.Args.idx_opt(x)`, one word) gives the same launch: the same paths, output bytes, messages
  and exit code.
- It covers the machine's report, not the process. With the driver's index errors ("cannot index
  <path>", ...), the process exits 2 where the machine's code is 0, and the law's comment says
  so.
- Repeated options are dropped one at a time. A line with `-o`, `-O` and `-W` drops each in turn
  through law `output` and law `index`.

**A new law `index_sink`** (decision 5):
- wherever the parser expects an option, adding one index option `x` gives the same
  `route(argv) = Route{B.Args.output(argv), B.Args.threads(argv)}`. So `-W` writes the same bytes
  to the same place in the same way, with the same threads.
- Its only premises are `he` and `hx`.
- With `B.Args.index` built on `Args.sink`'s `Sink`, the index is that of the file the driver
  writes, by definition.

**Why a new law, not a wider `out_opt`.** Law `output` and its premise `B.Args.out_opt` are
approved. Widening `out_opt` would change the meaning of an approved definition, even though it
would make the law stronger. A new law leaves them as they are. It takes a dozen lines, and
its proof reuses `FT.same_parse` and `FO.texts_drop`.

**`index_ok`, `output_ok`'s counterpart:** `B.Args.index(argv)` is `Some` exactly when
`B.Args.parse(argv)` is. The driver calls `Args.index` only after `Norm.start` gave `Begin`, and
treats `None` as "internal error: no index", which never happens.

**How the parser carries it.** `Drv` gains a fifth field, `idx: Maybe<IFmt>`, read by `Drv.idx`.
The `ArgSt` record keeps its 8 fields, so the parser's and proofs' `ArgSt{...}` patterns stay as
they are. The existing
`Drv{...}` patterns gain one variable: 7 in `types.bend`, 3 in `proof_f_args.bend`.
`Args.word`'s pick chain gains one branch before the VCF-path fallback: a word with
`Args.wfmt(x)` set stores it, and `keep` does not record it.

**Law machine's comment changes:**
- a new bullet in "What this law does not cover" describes the trusted index writer: the order at
  the open, how lines are parsed and pushed, when and how the index is saved, the end cases, and
  what each kind of run leaves;
- its list of driver errors gains the index errors (next sections).

`LAWS.bend`, `run.bend` and law `output` do not change.

**What stays trusted, and how it is tested instead:**
- the line parse (`tbx_parse1`), the push (`hts_idx_push`) and the virtual offsets;
- finishing and saving the index;
- the order at the open, the temporary file, the removals and the rename.

All of it is tested against `tabix -p vcf` and `bcftools index` of the same file: the index must
be byte-identical, and "cannot index" must come exactly when they refuse (test plan below).

## The draft (scratch copy, checked)

The exact edits, as diffs against this branch's tree.

`types.bend`:

```diff
--- a/types.bend
+++ b/types.bend
@@ -712,21 +712,24 @@
 #   w: the sorting window (-w, default 1000, at least 1).
 #   args: the command-line arguments that decide the output, recorded in the
 #     header: all those after "norm" except --threads, -o and -O and their
-#     values (which only size the program's work, or choose how and where the
-#     text is written), so the text is the same for every N, every output
-#     file and every output type.
+#     values, and -W (which only size the program's work, choose how and
+#     where the text is written, or ask for its index), so the text is the
+#     same for every N, every output file and type, with or without an
+#     index.
 type Opts is Data:
   Opts{strict: Bool, w: Nat, args: List<&2, String>}
 
 # A parsed command line: the options, the FASTA path, the VCF path. The thread
-# count (--threads) and the output options (-o, -O) are not part of it (see
-# Args.threads, Args.output).
+# count (--threads), the output options (-o, -O) and the index option (-W)
+# are not part of it (see Args.threads, Args.output, Args.index).
 type Cfg is Data:
   Cfg{opts: Opts, ref: String, vcf: String}
 
-# The usage message, printed on a usage error (exit code 2).
+# The usage message, printed on a usage error (exit code 2). Its second line
+# says that -W replaces an old index of the -o file (the README says what a
+# run without -W leaves).
 def usage() -> String:
-  "usage: framebender norm -f ref.fa [-c e|w] [-w N] [--threads N] [-o FILE] [-O v|z|z0-9] in.vcf\n"
+  "usage: framebender norm -f ref.fa [-c e|w] [-w N] [--threads N] [-o FILE] [-O v|z|z0-9] [-W[=csi|tbi]] in.vcf\n  -W also removes FILE's old .csi/.tbi\n"
 
 # The largest thread count --threads accepts: a chosen limit, the most worker
 # threads Bend's runtime runs and the size of the driver's tables.
@@ -749,31 +752,47 @@
 type OType is Data:
   OType{z: Bool, level: Maybe<&2, Nat>}
 
+# An index format, as -W names it: CSI (the default) or TBI.
+type IFmt is Data:
+  Csi{}
+  Tbi{}
+
 # What the command line says about how the program works and writes, never
 # about what it writes: the thread count (--threads N), the output path (-o),
-# the output type (-O: z True for BGZF) and the compression level (the digit
-# of -O z0 ... z9). For each, the last one given; a later -O without a digit
-# keeps the level, as in bcftools 1.24 (-Oz0 -Oz is level 0).
+# the output type (-O: z True for BGZF), the compression level (the digit
+# of -O z0 ... z9) and the index format (-W). For each, the last one given; a
+# later -O without a digit keeps the level, as in bcftools 1.24 (-Oz0 -Oz is
+# level 0).
 type Drv is Data:
-  Drv{thr: Maybe<&2, Nat>, out: Maybe<&2, String>, z: Maybe<&2, Bool>, lvl: Maybe<&2, Nat>}
+  Drv{thr: Maybe<&2, Nat>, out: Maybe<&2, String>, z: Maybe<&2, Bool>, lvl: Maybe<&2, Nat>, idx: Maybe<&2, IFmt>}
 
 def Drv.none() -> Drv:
-  Drv{None{}, None{}, None{}, None{}}
+  Drv{None{}, None{}, None{}, None{}, None{}}
 
 def Drv.thr(d: Drv) -> Maybe<&2, Nat>:
   match d:
-    case Drv{t, o, z, l}:
+    case Drv{t, o, z, l, i}:
       t
 
 def Drv.set_thr(+n: Nat, d: Drv) -> Drv:
   match d:
-    case Drv{t, o, z, l}:
-      Drv{Some{n}, o, z, l}
+    case Drv{t, o, z, l, i}:
+      Drv{Some{n}, o, z, l, i}
 
 def Drv.set_out(+x: String, d: Drv) -> Drv:
   match d:
-    case Drv{t, o, z, l}:
-      Drv{t, Some{x}, z, l}
+    case Drv{t, o, z, l, i}:
+      Drv{t, Some{x}, z, l, i}
+
+def Drv.idx(d: Drv) -> Maybe<&2, IFmt>:
+  match d:
+    case Drv{t, o, z, l, i}:
+      i
+
+def Drv.set_idx(m: Maybe<&2, IFmt>, d: Drv) -> Drv:
+  match d:
+    case Drv{t, o, z, l, i}:
+      Drv{t, o, z, l, m}
 
 def Drv.keep_lvl(m: Maybe<&2, Nat>, l: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
   match m:
@@ -784,8 +803,8 @@
 
 def Drv.set_typ(x: OType, d: Drv) -> Drv:
   match x d:
-    case OType{y, m} Drv{t, o, z, l}:
-      Drv{t, o, Some{y}, Drv.keep_lvl(m, l)}
+    case OType{y, m} Drv{t, o, z, l, i}:
+      Drv{t, o, Some{y}, Drv.keep_lvl(m, l), i}
 
 # Two characters are equal ignoring ASCII case (b in lower case).
 def Args.ceq(a: Char, b: Char) -> Bool:
@@ -826,9 +845,19 @@
   Bool.pick(Maybe<&2, OType>, String.eq(x, "z"), Some{OType{True{}, None{}}},
   Args.otype.lvl(String.starts_with(x, "z") && Nat.is_eq(String.length(x), 2n), Pos.read(String.drop(x, 1n)))))
 
+# The index option, one word, in the eight forms bcftools 1.24 documents: -W
+# or --write-index (CSI), -Wcsi, -Wtbi, -W=csi, -W=tbi, --write-index=csi or
+# --write-index=tbi. None for any other word (bcftools' abbreviations and
+# --write-index==tbi are not taken). (A value in the next word is not read:
+# in bcftools, -W tbi is -W and the word tbi.)
+def Args.wfmt(+x: String) -> Maybe<&2, IFmt>:
+  Bool.pick(Maybe<&2, IFmt>, String.eq(x, "-W") || String.eq(x, "--write-index") || String.eq(x, "-Wcsi") || String.eq(x, "-W=csi") || String.eq(x, "--write-index=csi"), Some{Csi{}},
+  Bool.pick(Maybe<&2, IFmt>, String.eq(x, "-Wtbi") || String.eq(x, "-W=tbi") || String.eq(x, "--write-index=tbi"), Some{Tbi{}}, None{}))
+
 # The command line read so far; ok turns False on any error. drv: the thread
-# count and the output options; keep: the arguments recorded in the header
-# (all but --threads, -o, -O and their values), in order.
+# count, the output options and the index format; keep: the arguments
+# recorded in the header (all but --threads, -o, -O and their values, and
+# -W), in order.
 type ArgSt is Data:
   ArgSt{pend: Pend, strict: Bool, w: Maybe<&2, Nat>, drv: Drv, ref: Maybe<&2, String>, vcf: Maybe<&2, String>, ok: Bool, keep: List<&2, String>}
 
@@ -851,7 +880,8 @@
       Bool.pick(ArgSt, String.eq(x, "-o"), ArgSt{POut{}, s, w, t, r, v, ok, k},
       Bool.pick(ArgSt, String.eq(x, "-O"), ArgSt{PType{}, s, w, t, r, v, ok, k},
       Bool.pick(ArgSt, String.starts_with(x, "-O"), Args.typ(Args.otype(String.drop(x, 2n)), ArgSt{PType{}, s, w, t, r, v, ok, k}),
-      ArgSt{PNone{}, s, w, t, r, Some{x}, ok && Bool.not(opt) && Maybe.is_none(&2, String, v), kx})))))))
+      Bool.pick(ArgSt, Maybe.is_some(&2, IFmt, Args.wfmt(x)), ArgSt{PNone{}, s, w, Drv.set_idx(Args.wfmt(x), t), r, v, ok, k},
+      ArgSt{PNone{}, s, w, t, r, Some{x}, ok && Bool.not(opt) && Maybe.is_none(&2, String, v), kx}))))))))
 
 def Args.win(m: Maybe<&2, Nat>, st: ArgSt) -> ArgSt:
   match m st:
@@ -868,7 +898,7 @@
       ArgSt{PNone{}, s, w, t, r, v, False{}, k}
 
 # The state after one more argument x. Every argument is recorded (keep)
-# except --threads, -o and -O (glued -OT too) and their values.
+# except --threads, -o and -O (glued -OT too) and their values, and -W.
 def Args.step(st: ArgSt, +x: String) -> ArgSt:
   match st:
     case ArgSt{PNone{}, s, w, t, r, v, ok, k}:
@@ -914,9 +944,10 @@
 # The command line after the program name: "norm", then the options -f FASTA
 # (required), -c e or -c w (default e), -w N (N at least 1, default 1000),
 # --threads N (N from 1 to Args.max_threads()), -o PATH (any word not ending
-# in .bcf, in any case), -O T or -OT (T: v, z, z0 to z9) in any order, and one
-# VCF path. None for anything else (a usage error). For -c, -w, --threads, -o
-# and -O every one given must be valid, and the last one counts.
+# in .bcf, in any case), -O T or -OT (T: v, z, z0 to z9), the index option
+# (Args.wfmt) in any order, and one VCF path. None for anything else (a usage
+# error). For -c, -w, --threads, -o and -O every one given must be valid, and
+# the last one counts (for -W too).
 def Args.parse(argv: List<&2, String>) -> Maybe<&2, Cfg>:
   match argv:
     case Nil{}:
@@ -1035,7 +1066,7 @@
 # Args.level().
 def Args.sink(d: Drv) -> Sink:
   match d:
-    case Drv{t, +o, z, l}:
+    case Drv{t, +o, z, l, i}:
       Sink{Args.file(o), Args.z.of(Args.ext.of(o), z), Maybe.default(&2, Nat, l, Args.level())}
 
 def Args.sink.done(st: ArgSt) -> Maybe<&2, Sink>:
@@ -1061,3 +1092,68 @@
       None{}
     case +cmd <> +rest:
       Args.output.if(String.eq(cmd, "norm"), rest)
+
+# ---------------------------------------------------------------------------
+# The index option (it asks for the output's index; law index)
+# ---------------------------------------------------------------------------
+
+# One index option, one word (law index's premise).
+def Args.idx_opt(+x: String) -> Bool:
+  Maybe.is_some(&2, IFmt, Args.wfmt(x))
+
+# The index file's suffix, appended to the -o path as bcftools 1.24 does.
+def IFmt.ext(f: IFmt) -> String:
+  match f:
+    case Csi{}:
+      ".csi"
+    case Tbi{}:
+      ".tbi"
+
+# Whether the output is indexed, and where.
+#   NoIdx: no -W;
+#   Idx{fmt, path}: the index of the -o file, in format fmt, at path (the -o
+#     path, as Args.output's Sink names it, and IFmt.ext(fmt));
+#   BadIdx: -W, but the output is stdout or plain text: an index needs a BGZF
+#     file named by -o (as in bcftools 1.24, which also refuses both).
+type Idx is Data:
+  NoIdx{}
+  Idx{fmt: IFmt, path: String}
+  BadIdx{}
+
+# The index of the output Sink s, for the index format m (None: no -W): the
+# Sink's own file and type, so the index is always that of the file the
+# driver writes.
+def Args.idx.mk(m: Maybe<&2, IFmt>, s: Sink) -> Idx:
+  match m s:
+    case None{} _:
+      NoIdx{}
+    case Some{+x} Sink{Some{+p}, True{}, l}:
+      Idx{x, p ++ IFmt.ext(x)}
+    case Some{x} _:
+      BadIdx{}
+
+def Args.index.done(st: ArgSt) -> Maybe<&2, Idx>:
+  match st:
+    case ArgSt{PNone{}, s, w, +t, Some{r}, Some{v}, True{}, k}:
+      Some{Args.idx.mk(Drv.idx(t), Args.sink(t))}
+    case _:
+      None{}
+
+def Args.index.if(ok: Bool, rest: List<&2, String>) -> Maybe<&2, Idx>:
+  match ok:
+    case True{}:
+      Args.index.done(Args.go(rest, Args.init()))
+    case False{}:
+      None{}
+
+# The index of a command line Args.parse accepts, built on the Sink
+# Args.output gives for it (Args.idx.mk); None for every command line it
+# refuses. The driver writes the index there once the output is complete;
+# law index (MACHINE.bend) says -W changes nothing in the machine's report,
+# law index_sink that it changes neither Args.output nor Args.threads.
+def Args.index(argv: List<&2, String>) -> Maybe<&2, Idx>:
+  match argv:
+    case Nil{}:
+      None{}
+    case +cmd <> +rest:
+      Args.index.if(String.eq(cmd, "norm"), rest)
```

`MACHINE.bend`:

```diff
--- a/MACHINE.bend
+++ b/MACHINE.bend
@@ -192,6 +192,55 @@
 #   Decompressed, the file is a prefix of the output bytes: all of them when
 #   the machine finished. After a failed write nothing more is written to the
 #   output.
+# - The index, as B.Args.index(argv) says (laws index and index_sink): for
+#   Idx{fmt, path} (-W with a BGZF -o file), at the open of the -o file, in
+#   this order: (1) it is opened without being emptied, and without waiting
+#   for a reader (a FIFO with no reader is refused, not waited on); (2) it
+#   must be a regular file and not an input (as above); (3) neither
+#   <-o path>.csi nor <-o path>.tbi may be a directory, a name that cannot be
+#   looked at, or (itself, or the file a symlink there names) the -o file, an
+#   input or stderr's regular file; (4) a temporary file is created next to
+#   path, path.tmp (path.tmp1, path.tmp2, ... when that name exists), mode
+#   0666 less the umask; (5) each of <-o path>.csi and <-o path>.tbi that
+#   exists is renamed aside, to <name>.old (.old1, ... when that name exists;
+#   never replacing a file: renameat2 with RENAME_NOREPLACE, or, where the
+#   file system lacks it, link then unlink; where it has neither, the run is
+#   refused); (6) the -o file is emptied, and if that fails the
+#   old indexes are renamed back; (7) the renamed old indexes are removed (an
+#   index of either format there describes the file being replaced, and
+#   htslib reads .csi before .tbi; if one cannot be removed, it stays as
+#   <name>.old, a name htslib never reads, and the run goes on). A failure in
+#   (1) to (6) leaves the old -o file and both old indexes as they were (a -o
+#   file that did not exist stays, empty), except that an index whose move
+#   back fails stays as <name>.old beside the unchanged -o file (the message
+#   is the step's own: "cannot write <path>" or "cannot write <name>"). Each line of the output is parsed as
+#   tabix -p vcf parses it (htslib 1.24's tbx_parse1, on the compressor
+#   threads; a line holding END= under a lock, as tbx_parse1 then touches a
+#   static; lines longer than a block are joined first) and pushed
+#   (hts_idx_push, in order, by the writer thread, before the block's bytes
+#   are freed) at the virtual offset where it ends (each block's address in
+#   the file and the offset in its text, as bgzf_tell gives them to a reader;
+#   a last line without LF at the end-of-file block's address). Only for exit
+#   code 0 is the index finished (at the end-of-file block's address) and,
+#   after the end-of-file block is written and the file closed, saved
+#   (hts_idx_save_as, given a name htslib cannot take for a URL: ./ before a
+#   relative path) to the temporary file, then renamed to path: the index is
+#   byte for byte what tabix -p vcf (TBI) or bcftools index (CSI, min_shift
+#   14) writes for the -o file. Once the open is done, a run that does not
+#   exit 0 leaves no index at either name; no run leaves the temporary file
+#   unless it is killed or Bend's runtime stops it (with _exit: out of memory,
+#   a Nat past 2^48), and a stray path.tmp or <name>.old is a file htslib
+#   never reads. On a normal exit, the index is there exactly
+#   when the run exits 0, and the -o file is then complete; when the index
+#   cannot be saved or renamed, the end-of-file block is cut off again (as
+#   when closing fails) and the run exits 2, and as there, the file may keep
+#   the block when that take-back fails, or when the duplicate descriptor's
+#   close fails after the rename (the new index is then removed). When a line
+#   cannot be indexed, the run continues as without -W, and at the end, for
+#   exit code 0 only, after all of the machine's messages, it writes no
+#   end-of-file block and exits 2 ("cannot index <path>"); for any other exit
+#   code the run is the run without -W, with no index. htslib's own log
+#   messages are switched off.
 # - Answering each reference read Req{chrom, a, b} of an Ask, in order, with
 #   exactly truth(B.Fasta.parse(fasta), chrom, a, b): Unknown when the .fai has
 #   no such contig, else Known with the contig's length String.length(Contig.raw)
@@ -208,8 +257,28 @@
 #   file: it cannot be opened, written or closed), "error: output is an input
 #   <path>" (the -o file, of any type, a pipe or FIFO too, is the VCF, the
 #   FASTA or its .fai, or is stderr's regular file: refused before the file
-#   is emptied), "error: out of memory" (libdeflate's
-#   decompressor or compressor),
+#   is emptied; also <-o path>.csi or <-o path>.tbi with -W, itself or the
+#   file a symlink there names, before anything is changed), "error: out of
+#   memory" (libdeflate's decompressor or compressor; with -W, a table of the
+#   open), "error: -W needs a BGZF -o file" (B.Args.index is BadIdx: refused
+#   before any input is opened), "error: no index in this build <path>" (-W
+#   with BGZF output in a build with libdeflate and without htslib: see
+#   build.sh; a build without libdeflate says "no BGZF in this build"
+#   first), "error: cannot index <path> (not a regular file)" (the -o file,
+#   with -W; a FIFO with no reader too), "error: cannot index <path>" (with
+#   -W, for a run whose code is 0, after all of its messages: exactly when
+#   tabix -p vcf (TBI) or bcftools index (CSI) refuses the same file; known
+#   causes: a POS that htslib reads otherwise, such as one with a leading
+#   zero, octal to its strtoll, or 0x, on a line passed unchanged; a position
+#   (POS or INFO/END) past what the index holds: 2^29 for TBI, and for CSI
+#   past the levels the longest ##contig length sets, or 2^38 with no length;
+#   or no memory for the index), "error: cannot write <path>.csi" or ".tbi"
+#   (with -W: an index name that is a directory or cannot be looked at, the
+#   temporary file cannot be created, an old index cannot be renamed aside,
+#   all before anything is changed; or the index cannot be saved or
+#   renamed),
+#   "error: cannot write <path>.csi (it is the -o file)" (or .tbi: the -o
+#   path names that index, through a symlink or a hard link),
 #   "error: unsupported gzip <path> (not BGZF; ...)", "error:
 #   bad BGZF <path>" (also a BGZF VCF without the end-of-file block, as one cut
 #   at a block boundary), "error: no BGZF in this build <path>" (a BGZF VCF,
@@ -307,3 +376,57 @@
   for hb: {E.texts_ok(command(pre, List.append(&2, String, o, post)), fasta, cs) == True{} : Bool}
   {launch(Norm.start(command(pre, List.append(&2, String, o, post))), command(pre, List.append(&2, String, o, post)), fasta, vcf, cs)
     == launch(Norm.start(command(pre, post)), command(pre, post), fasta, vcf, cs) : Maybe<&2, Launch>}
+
+# -W asks for the output's index and changes nothing in the machine's report.
+# Wherever the parser expects an option (B.Args.expecting), adding one index
+# option x (B.Args.idx_opt: -W, -Wcsi, -Wtbi, -W=csi, -W=tbi, --write-index,
+# --write-index=csi or --write-index=tbi) gives the same paths and the same
+# report (output bytes, messages, exit code) as the same command line without
+# it. The driver then writes the index where B.Args.index says (see law
+# machine's comment). The law covers the machine's report, not the process:
+# the driver's own errors for the index ("-W needs a BGZF -o file", "cannot
+# index <path>", "cannot write <path>.csi", ...) are outside it, as law
+# machine's comment says, and with them the process exits 2 where the
+# machine's code is 0. It follows from law machine: parse gives the same Cfg
+# with or without x where an option is expected, and Opts.args does not
+# record it.
+law index:
+  for pre: List<&2, String>
+  for x: String
+  for post: List<&2, String>
+  for fasta: String
+  for vcf: String
+  for cs: List<&2, String>
+  for he: {B.Args.expecting(pre) == True{} : Bool}
+  for hx: {B.Args.idx_opt(x) == True{} : Bool}
+  for hf: {P.Fasta.plain(fasta) == True{} : Bool}
+  for h: {String.concat(cs) == vcf : String}
+  for hb: {E.texts_ok(command(pre, x <> post), fasta, cs) == True{} : Bool}
+  {launch(Norm.start(command(pre, x <> post)), command(pre, x <> post), fasta, vcf, cs)
+    == launch(Norm.start(command(pre, post)), command(pre, post), fasta, vcf, cs) : Maybe<&2, Launch>}
+
+# What the driver takes from a command line besides the machine's report:
+# where and how it writes the output (B.Args.output) and its thread count
+# (B.Args.threads).
+type Route is Data:
+  Route{sink: Maybe<&2, B.Sink>, thr: Maybe<&2, Nat>}
+
+def route(+argv: List<&2, String>) -> Route:
+  Route{B.Args.output(argv), B.Args.threads(argv)}
+
+# -W changes neither where and how the output is written nor the thread
+# count: wherever the parser expects an option (B.Args.expecting), adding one
+# index option x (B.Args.idx_opt) gives the same B.Args.output and the same
+# B.Args.threads as the command line without it. With law index, the run
+# with -W is the run without it, plus the index; B.Args.index is built on
+# B.Args.output's Sink (B.Args.idx.mk), so the index is that of the file the
+# driver writes. It follows from the parser: where an option is expected, x
+# changes only the index format the parser keeps (Drv.idx), which
+# B.Args.sink and B.Args.threads do not read.
+law index_sink:
+  for pre: List<&2, String>
+  for x: String
+  for post: List<&2, String>
+  for he: {B.Args.expecting(pre) == True{} : Bool}
+  for hx: {B.Args.idx_opt(x) == True{} : Bool}
+  {route(command(pre, x <> post)) == route(command(pre, post)) : Route}
```

`examples.bend`:

```diff
--- a/examples.bend
+++ b/examples.bend
@@ -295,6 +295,123 @@
 def oo_extra() -> {B.Args.out_opt(["-Oz", "x"]) == False{} : Bool}:
   {==}
 
+# --- The index option (-W; law index) ---------------------------------------
+
+# It changes nothing Args.parse returns, and is not recorded in the header.
+def idx_header() -> {B.Args.parse(["norm", "-W", "-f", "r.fa", "-o", "o.vcf.gz", "in.vcf"]) == Some{B.Cfg{B.Opts{True{}, 1000n, ["-f", "r.fa", "in.vcf"]}, "r.fa", "in.vcf"}} : Maybe<&2, B.Cfg>}:
+  {==}
+
+def idx_long() -> {B.Args.parse(["norm", "-f", "r.fa", "in.vcf", "--write-index=tbi"]) == B.Args.parse(["norm", "-f", "r.fa", "in.vcf"]) : Maybe<&2, B.Cfg>}:
+  {==}
+
+# Accepted with stdout or plain output too: Args.index says BadIdx, and the
+# driver refuses it ("-W needs a BGZF -o file").
+def idx_stdout_parse() -> {B.Args.parse(["norm", "-W", "-f", "r.fa", "in.vcf"]) == Some{B.Cfg{B.Opts{True{}, 1000n, ["-f", "r.fa", "in.vcf"]}, "r.fa", "in.vcf"}} : Maybe<&2, B.Cfg>}:
+  {==}
+
+# Refused: another format (bai, a format in upper case), an abbreviated long
+# form; a format in the next word is that word (here a second VCF path).
+def idx_bai() -> {B.Args.parse(["norm", "-Wbai", "-f", "r.fa", "in.vcf"]) == None{} : Maybe<&2, B.Cfg>}:
+  {==}
+
+def idx_upper() -> {B.Args.parse(["norm", "-W=TBI", "-f", "r.fa", "in.vcf"]) == None{} : Maybe<&2, B.Cfg>}:
+  {==}
+
+def idx_abbrev() -> {B.Args.parse(["norm", "--write", "-f", "r.fa", "in.vcf"]) == None{} : Maybe<&2, B.Cfg>}:
+  {==}
+
+def idx_next_word() -> {B.Args.parse(["norm", "-W", "tbi", "-f", "r.fa", "in.vcf"]) == None{} : Maybe<&2, B.Cfg>}:
+  {==}
+
+# B.Args.index: the -o path with .csi or .tbi; the last -W counts.
+def index_none() -> {B.Args.index(["norm", "-f", "r.fa", "-o", "o.vcf.gz", "in.vcf"]) == Some{B.NoIdx{}} : Maybe<&2, B.Idx>}:
+  {==}
+
+def index_csi() -> {B.Args.index(["norm", "-f", "r.fa", "-o", "o.vcf.gz", "-W", "in.vcf"]) == Some{B.Idx{B.Csi{}, "o.vcf.gz.csi"}} : Maybe<&2, B.Idx>}:
+  {==}
+
+def index_tbi() -> {B.Args.index(["norm", "-Wtbi", "-f", "r.fa", "-o", "o.vcf.gz", "in.vcf"]) == Some{B.Idx{B.Tbi{}, "o.vcf.gz.tbi"}} : Maybe<&2, B.Idx>}:
+  {==}
+
+def index_last() -> {B.Args.index(["norm", "-W=tbi", "-f", "r.fa", "--write-index", "-o", "o.vcf.gz", "in.vcf"]) == Some{B.Idx{B.Csi{}, "o.vcf.gz.csi"}} : Maybe<&2, B.Idx>}:
+  {==}
+
+def index_other_ext() -> {B.Args.index(["norm", "-W", "-Oz", "-f", "r.fa", "-o", "out.gz", "in.vcf"]) == Some{B.Idx{B.Csi{}, "out.gz.csi"}} : Maybe<&2, B.Idx>}:
+  {==}
+
+# The type is Args.output's: -Ov with a .vcf.gz path is BGZF (indexed); -Oz
+# with a .vcf path is plain (BadIdx).
+def index_ext_wins() -> {B.Args.index(["norm", "-W", "-Ov", "-f", "r.fa", "-o", "o.vcf.gz", "in.vcf"]) == Some{B.Idx{B.Csi{}, "o.vcf.gz.csi"}} : Maybe<&2, B.Idx>}:
+  {==}
+
+def index_plain_ext() -> {B.Args.index(["norm", "-W", "-Oz", "-f", "r.fa", "-o", "o.vcf", "in.vcf"]) == Some{B.BadIdx{}} : Maybe<&2, B.Idx>}:
+  {==}
+
+# Stdout (no -o, or -o -), and plain output to a file, cannot be indexed.
+def index_stdout() -> {B.Args.index(["norm", "-W", "-Oz", "-f", "r.fa", "in.vcf"]) == Some{B.BadIdx{}} : Maybe<&2, B.Idx>}:
+  {==}
+
+def index_dash() -> {B.Args.index(["norm", "-W", "-Oz", "-o", "-", "-f", "r.fa", "in.vcf"]) == Some{B.BadIdx{}} : Maybe<&2, B.Idx>}:
+  {==}
+
+def index_plain() -> {B.Args.index(["norm", "-W", "-f", "r.fa", "-o", "out.txt", "in.vcf"]) == Some{B.BadIdx{}} : Maybe<&2, B.Idx>}:
+  {==}
+
+def index_refused() -> {B.Args.index(["norm", "-W", "-o", "o.vcf.gz", "in.vcf"]) == None{} : Maybe<&2, B.Idx>}:
+  {==}
+
+# -W leaves the output and the thread count as they are.
+def idx_sink() -> {B.Args.output(["norm", "-Oz1", "-W", "-f", "r.fa", "-o", "o.vcf.gz", "in.vcf"]) == Some{B.Sink{Some{"o.vcf.gz"}, True{}, 1n}} : Maybe<&2, B.Sink>}:
+  {==}
+
+def idx_threads() -> {B.Args.threads(["norm", "-W", "--threads", "4", "-f", "r.fa", "-o", "o.vcf.gz", "in.vcf"]) == Some{4n} : Maybe<&2, Nat>}:
+  {==}
+
+# The index option, one word (law index's B.Args.idx_opt).
+def io_forms() -> {(B.Args.idx_opt("-W") && B.Args.idx_opt("-Wcsi") && B.Args.idx_opt("-Wtbi") && B.Args.idx_opt("-W=csi") && B.Args.idx_opt("-W=tbi") && B.Args.idx_opt("--write-index") && B.Args.idx_opt("--write-index=csi") && B.Args.idx_opt("--write-index=tbi")) == True{} : Bool}:
+  {==}
+
+def io_not() -> {(B.Args.idx_opt("-W=") || B.Args.idx_opt("-Wbai") || B.Args.idx_opt("--write-index=") || B.Args.idx_opt("-w")) == False{} : Bool}:
+  {==}
+
+# The other BGZF extensions, in any case: the suffix is appended to the path
+# as given.
+def index_bgz() -> {B.Args.index(["norm", "-W", "-f", "r.fa", "-o", "x.vcf.bgz", "in.vcf"]) == Some{B.Idx{B.Csi{}, "x.vcf.bgz.csi"}} : Maybe<&2, B.Idx>}:
+  {==}
+
+def index_upper_ext() -> {B.Args.index(["norm", "-Wtbi", "-f", "r.fa", "-o", "x.VCF.GZ", "in.vcf"]) == Some{B.Idx{B.Tbi{}, "x.VCF.GZ.tbi"}} : Maybe<&2, B.Idx>}:
+  {==}
+
+# --write-index tbi: the format is not read from the next word, which is the
+# VCF path (here the only one).
+def idx_tbi_path() -> {B.Args.parse(["norm", "-f", "r.fa", "--write-index", "tbi"]) == Some{B.Cfg{B.Opts{True{}, 1000n, ["-f", "r.fa", "tbi"]}, "r.fa", "tbi"}} : Maybe<&2, B.Cfg>}:
+  {==}
+
+def index_tbi_path() -> {B.Args.index(["norm", "-f", "r.fa", "-o", "o.vcf.gz", "--write-index", "tbi"]) == Some{B.Idx{B.Csi{}, "o.vcf.gz.csi"}} : Maybe<&2, B.Idx>}:
+  {==}
+
+# The index is built on the output's Sink (B.Args.idx.mk): BGZF to a file is
+# indexed, anything else with -W is BadIdx, no -W is NoIdx.
+def idx_mk_file() -> {B.Args.idx.mk(Some{B.Tbi{}}, B.Sink{Some{"o.vcf.gz"}, True{}, 6n}) == B.Idx{B.Tbi{}, "o.vcf.gz.tbi"} : B.Idx}:
+  {==}
+
+def idx_mk_plain() -> {B.Args.idx.mk(Some{B.Csi{}}, B.Sink{Some{"o.vcf"}, False{}, 6n}) == B.BadIdx{} : B.Idx}:
+  {==}
+
+def idx_mk_stdout() -> {B.Args.idx.mk(Some{B.Csi{}}, B.Sink{None{}, True{}, 6n}) == B.BadIdx{} : B.Idx}:
+  {==}
+
+def idx_mk_none() -> {B.Args.idx.mk(None{}, B.Sink{Some{"o.vcf.gz"}, True{}, 6n}) == B.NoIdx{} : B.Idx}:
+  {==}
+
+# Law index_sink on two lines: the same output and thread count with and
+# without -W.
+def route_w() -> {M.route(["norm", "-Wtbi", "-Oz1", "--threads", "4", "-f", "r.fa", "-o", "o.vcf.gz", "in.vcf"]) == M.Route{Some{B.Sink{Some{"o.vcf.gz"}, True{}, 1n}}, Some{4n}} : M.Route}:
+  {==}
+
+def route_same() -> {M.route(["norm", "-f", "r.fa", "-o", "o.vcf.gz", "in.vcf", "--write-index=csi"]) == M.route(["norm", "-f", "r.fa", "-o", "o.vcf.gz", "in.vcf"]) : M.Route}:
+  {==}
+
 # --- Whole runs ------------------------------------------------------------
 
 def fa() -> String:
```

`build.sh`:

```diff
--- a/build.sh
+++ b/build.sh
@@ -6,10 +6,30 @@
 #   ./build.sh [output]        (default: framebender next to this script)
 # A plain `bend main.bend -o framebender` still builds; that binary stops on a
 # BGZF VCF with "error: no BGZF in this build <path>".
+# The index (-W) needs htslib 1.24 built without libcurl, GCS and S3
+# (tools/build_htslib.sh installs it in ~/.local/opt/htslib-1.24-nocurl),
+# found by pkg-config (PKG_CONFIG_PATH, default that prefix) and linked
+# statically: its tbx_parse1 and hts_adjust_csi_settings are not exported by
+# libhts.so. FB_NO_HTSLIB=1 builds without it; -W then stops with "error: no
+# index in this build <path>".
 set -e
 here=$(dirname "$0")
 out=${1:-$here/framebender}
 export BEND_NO_TELEMETRY=1
+hts=
+if [ "${FB_NO_HTSLIB:-0}" != 1 ]; then
+  pfx=$HOME/.local/opt/htslib-1.24-nocurl
+  export PKG_CONFIG_PATH=${PKG_CONFIG_PATH:-$pfx/lib/pkgconfig}
+  need="-W needs htslib 1.24 built without libcurl: tools/build_htslib.sh installs it in $pfx (./configure --disable-libcurl --disable-gcs --disable-s3), found with PKG_CONFIG_PATH=$pfx/lib/pkgconfig; FB_NO_HTSLIB=1 builds without -W"
+  [ "$(pkg-config --modversion htslib 2>/dev/null)" = 1.24 ] || { echo "build.sh: no htslib 1.24 found by pkg-config. $need" >&2; exit 1; }
+  lib=$(pkg-config --variable=libdir htslib)/libhts.a
+  libs=$(pkg-config --variable=static_libs htslib)
+  case " $libs " in *" -lcurl "*) echo "build.sh: $lib is built with libcurl. $need" >&2; exit 1 ;; esac
+  for f in tbx_parse1 hts_adjust_csi_settings; do
+    nm "$lib" 2>/dev/null | grep -q " T $f\$" || { echo "build.sh: $lib does not define $f. $need" >&2; exit 1; }
+  done
+  hts="-DFB_HTSLIB $(pkg-config --cflags htslib) $lib $libs"
+fi
 tmp=$(mktemp -d)
 trap 'rm -rf "$tmp"' EXIT
 bend "$here/main.bend" -o "$tmp/framebender.c"
@@ -61,4 +81,4 @@
   print "    return;"
   print "  }"
 }' "$c" > "$tmp/patched.c"
-${CC:-clang} -std=c11 -O3 -DFB_LIBDEFLATE "$tmp/patched.c" -lpthread -lm -ldeflate -o "$out"
+${CC:-clang} -std=c11 -O3 -DFB_LIBDEFLATE "$tmp/patched.c" $hts -lpthread -lm -ldeflate -o "$out"
```

`tools/build_htslib.sh` (new):

```diff
--- /dev/null
+++ b/tools/build_htslib.sh
@@ -0,0 +1,27 @@
+#!/bin/sh
+# Builds and installs the htslib that build.sh links for -W (phase J): htslib
+# 1.24, static, without libcurl, GCS and S3, so that the binary does not pull
+# in libcurl and libcrypto and htslib never opens a URL.
+#   tools/build_htslib.sh [PREFIX] [TARBALL]
+# PREFIX defaults to ~/.local/opt/htslib-1.24-nocurl; TARBALL to a download of
+# the 1.24 release, checked against its SHA-256. Then build with
+#   PKG_CONFIG_PATH=PREFIX/lib/pkgconfig ./build.sh
+set -e
+prefix=${1:-$HOME/.local/opt/htslib-1.24-nocurl}
+tarball=$2
+sum=28a8de191381c7a97a35675ceac76fa1ea95e7b678d6a2e9d600a7874e4077de
+tmp=$(mktemp -d)
+trap 'rm -rf "$tmp"' EXIT
+if [ -z "$tarball" ]; then
+  tarball=$tmp/htslib-1.24.tar.bz2
+  curl --proto '=https' --tlsv1.2 -fsSL -o "$tarball" https://github.com/samtools/htslib/releases/download/1.24/htslib-1.24.tar.bz2
+fi
+if command -v sha256sum > /dev/null; then got=$(sha256sum < "$tarball"); else got=$(shasum -a 256 < "$tarball"); fi
+[ "${got%% *}" = "$sum" ] || { echo "build_htslib.sh: $tarball is not htslib 1.24's release (SHA-256)" >&2; exit 1; }
+tar -xjf "$tarball" -C "$tmp"
+cd "$tmp/htslib-1.24"
+./configure --prefix="$prefix" --disable-libcurl --disable-gcs --disable-s3 --with-libdeflate > "$tmp/configure.log" 2>&1 \
+  || { cat "$tmp/configure.log" >&2; exit 1; }
+make -j"$(nproc 2>/dev/null || echo 4)" > "$tmp/make.log" 2>&1 || { tail -20 "$tmp/make.log" >&2; exit 1; }
+make install > "$tmp/install.log" 2>&1 || { tail -20 "$tmp/install.log" >&2; exit 1; }
+echo "htslib 1.24 (no libcurl) in $prefix: PKG_CONFIG_PATH=$prefix/lib/pkgconfig ./build.sh"
```

## The driver (trusted; for the driver review)

### The choice: on the fly, with htslib's own parser

The brief names two ways; a third came up:
- **A: on the fly.** `hts_idx_init`/`hts_idx_push`/`hts_idx_finish`/`hts_idx_save_as`, fed with
  the virtual offsets the writer knows.
- **B: after the run.** `tbx_index` (the loop `tbx_index_build3` runs) on the finished file.
- **A′: a second reader of the stream.** The same compressed stream also goes to a thread that
  runs htslib's public `tbx_index` on it as it is written.

All three were prototyped in scratch (`data/tmp/index/proto/`). Each is byte-identical to the
reference tools on every input tried. All three reviewers accepted A.

**Whole genome** (`data/hg002.all.vcf`, `-c w -Oz`, CPUs 0–15, `nice -n 19`, under the bench
lock, interleaved, 3 rounds: `data/tmp/index/bench3.txt`; the A and bcftools rows also come from
`bench1.txt` and `bench4.txt`; round 1 rows from `bench5.txt`):

| run | wall |
|---|---|
| framebender `-Oz`, no index | 2.85–3.03 s |
| prototype binary, index off (htslib linked) | 2.84–3.01 s |
| **A: on-the-fly CSI** | **3.26–3.42 s** |
| A: on-the-fly TBI | 3.43 s |
| A′: `fb -Oz \| tee \| tbx_index` (4 threads) | 3.73–3.89 s |
| B: `fb -Oz`, then `tbx_index` of the file (4 threads) | 4.35–4.56 s |
| framebender `-Oz1`, no index | 2.05–2.16 s |
| A: `-Oz1`, on-the-fly CSI | 2.50–2.61 s |
| `bcftools norm -Oz -W --threads 16` | 6.38–6.62 s |
| `bcftools norm -Oz --threads 16` | 6.05–6.26 s |
| round 1: framebender `-Oz`, no index (`bench6.txt`) | 2.87–3.03 s |
| round 1: A, CSI, with the `END=` lock | 3.33–3.41 s |
| round 1: A, CSI, no test and no lock | 3.27–3.43 s |

**Indexing alone** (`bench1.txt`, `bench2.txt`):

| run | wall |
|---|---|
| `tbx_index` of the finished file, 1 thread | 1.95–2.01 s |
| same, 4 threads (decompression in parallel) | 1.47–1.49 s |
| same, 16 threads | 1.48–1.51 s |
| `bcftools index --threads 16` | 1.59–1.63 s |
| `tabix -p vcf -@16` | 1.58–1.60 s |
| the parse-and-push loop alone (`pidx`: `tbx_parse1` + `hts_idx_push`, 1 thread) | 1.55–1.64 s |

**Peak memory** (`bench4.txt`):
- whole genome: 335 MB without the index, 354 MB with it;
- the 1000 Genomes slice: 234 MB without, 239–243 MB with it;
- `bcftools norm -W`: 31 MB.

**Index sizes, whole genome:** CSI 1,408,066 bytes, TBI 1,650,025 bytes.

**What the numbers say:**
- The floor of every approach is htslib's line parse. `tbx_parse1` walks every byte of every line,
  2.8 GB of text here, in about 1.5 s on one thread. Decompressing again in parallel is nearly
  free, so B and A′ are bound by the parse.
- **B** adds that 1.5 s after the run (4.35–4.56 s).
- **A′** overlaps it, but one thread parses the whole stream, so it trails the run (3.73–3.89 s).
- **A** parses each block on the compressor thread that compresses it, so the parse runs on 16
  threads. Only the ordered push is serial. It costs 0.4–0.55 s, which has not been broken down
  yet: the parse's CPU on the same 16 CPUs, the serial push, and the last blocks of each buffer
  waiting for their parse. Step 2 can profile it.
- **The lock of decision 1** costs nothing measurable. Its range overlaps the range without the
  lock on chr22 with `END=` on every record, on chr22 with 2% of the ENDs below POS, and on the
  whole genome (Round 1, decision 1). On `END=`-heavy input, framebender's own END check
  dominates by far.
- **Picked: A.** It is the fastest by 0.4 s over A′ and 1.1 s over B. It keeps the lead over
  bcftools at 1.9–2.0× (B would give 1.45×). It never reads the output back.

**The cost of A: two htslib functions that are not public.**
- `tbx_parse1` and `hts_adjust_csi_settings` are global in `libhts.a`, but hidden: they are not
  exported by `libhts.so` and not declared in its headers. `tbx_intv_t`, the struct
  `tbx_parse1` fills, is defined only in `tbx.c`.
- **So the driver links `libhts.a` statically**, and declares both functions and the struct with
  htslib 1.24's layout. Three guards:
  - build.sh requires htslib 1.24 exactly (`pkg-config --modversion`);
  - `nm` must show that `libhts.a` defines both functions;
  - `io64.c` stops at compile time on `HTS_VERSION != 102400`, and has a `_Static_assert` on
    `tbx_intv_t`'s field offsets and size.
- **The test suite guards them too:** the index must be byte-identical to `tabix 1.24`'s.
- **`tbx_parse1`'s one piece of shared state** is the function-static `reported` (`tbx.c:218`). It
  is read and written when a valid-looking INFO/END is not past POS, and only gates a log line;
  the log is off anyway. It is still a data race between compressor threads, so a line holding
  `END=` is parsed under a mutex (decision 1). The other statics `tbx_parse1` reaches are
  read-only (`tbx_conf_vcf`).
- **Small parts of `tbx_index` are reproduced in `io64.c`,** as they are static in `tbx.c`: the
  `##contig` length scan (10 lines), the metadata (`tbx_set_meta`, 25 lines, with its big-endian
  swap), the level formula when there is no length, the empty index's settings, the meta-line
  and CR rules of `bgzf_getline`, and the name-to-id order. htslib's licence (MIT/Expat) allows
  that, with the attribution in a comment.
- **The fallbacks, if a later round rejects this:**
  - A′ uses only the public API, at +0.4 s more than A;
  - B is the simplest, at +1.5 s, and works only for regular files.

  Both need about 100 fewer lines in the driver.

### Building the index (`io64.c`)

With `-W`, from the first block:

- **The compressor thread** of each block, after compressing it, parses the block's whole lines
  (`idx_scan` in the prototype). If the block starts inside a line, its first line starts after
  the first LF. For each line it keeps one entry:
  - its end in the block, after the LF;
  - its kind: a meta line (starts with `#`), a record, or a line `tbx_parse1` refuses;
  - for a record: beg, end, and CHROM's place in the block;
  - for a `##contig` line: its length.

  The parse works on a copy of the line with the CR removed, as `bgzf_getline` returns it. A
  line holding `END=` is parsed under `io64_ix_mu`. A failed allocation marks the block: its
  index is then bad.
- **The writer thread** writes the blocks in order, and knows each block's address in the file
  (the sum of the sizes written before it). It takes each block's entries in order:
  - a meta line sets the first offset; a `##contig` line before the first record sets the
    longest contig (CSI);
  - the first record creates the index (`hts_idx_init`, with the levels set);
  - each record gets its contig id: the last name is cached, else a hash in order of first
    appearance. It is pushed with `hts_idx_push` at the virtual offset of its line's end: `addr <<
    16 | offset` inside the block, or `(addr + size) << 16` at the block's end.
  - A line that runs past the block (only a line longer than a block, or the header's long-line
    case) is carried. The writer appends the next blocks' bytes to it until its LF, then parses it
    itself.
- **Memory order (decision 8):**
  - the writer indexes a block (`idx_block`) before it frees the block's copy and before it counts
    the block as written;
  - `Io.out_write` frees the machine's buffer only after `io64_out_drain` returns, so after every
    block inside it is indexed;
  - the bytes of a carried line are copied inside `idx_block`;
  - the last short blocks (`io64_out_tail` at `Io.out_close`) are copies, indexed the same way.
- **The end cases (decision 16),** kept as `tbx_index` has them, so that a rewrite does not
  "correct" them:
  - a last line with no LF is pushed at the end-of-file block's address, offset 0. `bgzf_getline`
    moves to the next block even without the delimiter;
  - `hts_idx_finish` gets that same address: where the 28-byte end-of-file block is written, not
    the offset after it.
- **An index failure** (decision 4) is a line `tbx_parse1` refuses, a push `hts_idx_push`
  refuses, or no memory. It sets the index's own flag, never the output's error:
  - the writer stops indexing and keeps writing the data, and the run goes on as without `-W`;
  - at `Io.out_close(c)`, for c ≠ 0 the flag is ignored: no index, and the run is byte for byte
    the run without `-W`;
  - for c = 0, after all of the machine's messages, the end-of-file block is not written, and the
    run gives "cannot index <path>", exit 2.

  So what is printed never depends on thread timing.
- **htslib's log is switched off** (`hts_set_log_level(HTS_LOG_OFF)`) once `-W` is set. Its
  warnings (POS 0, INFO/END below POS) would otherwise add lines to stderr on runs that succeed,
  and the messages must be those of the run without `-W`.

**When the index fails (decision 6).** "cannot index" comes exactly when `tabix -p vcf` (TBI) or
`bcftools index` (CSI) refuses the same file. On a run with code 0, the output is grouped by CHROM
and sorted by POS as `Pos.read` reads it (laws `sorted`, `grouped_in`). The known ways htslib
still refuses it:
- **a POS htslib reads otherwise:** a leading zero (`strtoll` base 0 reads it as octal, up to the
  first 8 or 9), or `0x`. This is only possible on a line framebender passes unchanged: out of
  scope, or `-c w`'s problem lines. framebender rewrites the POS of a record it judges (`015884846`
  comes out as `15884846`). Checked: `chr22 015884846 … C <DEL>` under `-c e` is refused by
  `tabix` and gives "cannot index".
- **a position past what the index holds,** POS or INFO/END:
  - TBI: 2^29;
  - CSI: past the levels the longest `##contig` length sets (that length + 256, rounded up by the
    level formula);
  - CSI with no length: 2^38 (8 levels).

  A `##contig` length past 2^41 moves `min_shift` instead (`hts_adjust_csi_settings`, whose
  warning is off).
- **no memory** for the index.

A MALFORMED POS and a blank body line are not among them: framebender stops on both (exit 1),
under `-c w` too, before the line is written.

### The files

**At the open of the `-o` file** (the first write, after the first VCF piece was read), with `-W`,
in this order (decision 2). Each check comes before anything is changed:
1. **The open:** `O_WRONLY | O_CREAT | O_NONBLOCK`, without emptying the file. A FIFO with no
   reader fails at once (ENXIO) instead of blocking (decision 3): "cannot index <path> (not a
   regular file)". O_NONBLOCK is then cleared.
2. **The `-o` file:**
   - phase H's checks: it is not an input or stderr's file;
   - it must be a regular file: otherwise "cannot index <path> (not a regular file)". A FIFO with
     a reader (who then sees an empty stream), `/dev/stdout` or `/dev/null` cannot be indexed,
     and `/dev/null.csi` is not created.
3. **The index names,** `<path>.csi` and `<path>.tbi`, each looked at with `lstat` (ENOENT is
   fine):
   - a directory, or a name `lstat` cannot look at (EACCES, ENAMETOOLONG, ...): "cannot write
     <path>.csi";
   - the `-o` file itself, through a symlink or a hard link: "cannot write <path>.csi (it is the
     -o file)". This is GPT's case: `-o` a symlink to its own `.csi`, which the removal of the old
     indexes would otherwise unlink;
   - an input or stderr's file, itself or the file a symlink there names (`stat`): "output is an
     input <path>.csi";
   - a name that `stat` resolves to a directory, through a symlink (driver review 9, finding 3):
     "cannot write <path>.csi". Otherwise a `-o` path through that link would be replaced by the
     index.

   **For TBI, the names htslib reads first** (driver review 9, finding 2). htslib 1.24
   (`hts_idx_check_local`, used by `tabix`, `bcftools view -r` and `tbx_index_load3`) tries, for
   the `-o` path `f`: `f.csi`, then `<stem>.csi` (`f` up to its last `.` after the first byte,
   with `.csi`: `o.vcf.csi` for `o.vcf.gz`, `d.csi` for `d.x/out`), then `f.tbi`, then
   `<stem>.tbi`, and reads the first that `stat` finds. `f.csi` is moved aside in step 5. While
   `<stem>.csi` exists, `-W=tbi` is refused with nothing changed: "cannot write <path>.tbi
   (htslib would read <stem>.csi first)" (code 2012). The file is not removed: it may be the index
   of another file (`o.vcf`). A dangling symlink there is not refused, since `stat` does not find
   it. A CSI comes first in every order, so nothing hides it.
4. **The temporary file,** `<index>.tmp` (`.tmp1`, `.tmp2`, ... when that name exists), is created
   with `O_CREAT | O_EXCL`, mode 0666 less the umask, and closed. If it cannot be created (a
   directory without write permission, a name past `NAME_MAX`): "cannot write <index>"
   (decision 9).
5. **The old indexes are renamed aside** (decision 20). Each of `<path>.csi` and `<path>.tbi` that
   exists goes to `<name>.old` (`.old1`, `.old2`, ... when that name exists), with `renameat2`
   and `RENAME_NOREPLACE`, so no file is ever replaced. Where the file system refuses
   `RENAME_NOREPLACE` (EINVAL, ENOSYS, EOPNOTSUPP: NFS, some FUSE file systems, old kernels), a
   move is `link(name, t)`, which never replaces a file either (EEXIST keeps the `.old1` loop),
   then `unlink(name)`. If that unlink fails, `t` is removed and the move fails, nothing
   changed. Where `link` is not supported either, the move fails: there is no check-then-rename,
   which could replace a file (decision 26). If one cannot be moved (EACCES; EPERM in a sticky
   directory, for an old index someone else owns), the one moved already is moved back:
   "cannot write <name>".
6. **The `-o` file is emptied** (`ftruncate`), as today, after the duplicate descriptor for phase
   H's take-back is made. If that fails, the old indexes are moved back.
7. **The moved old indexes are removed** (`unlink`). Either one described the file being
   replaced. If one cannot be removed, it stays as `<name>.old`, a name htslib never reads, and
   the run goes on with no message.

A failure in steps 1–6 leaves the old `-o` file and both old indexes as they were, except that
an index whose move back fails stays as `<name>.old` beside the unchanged `-o` file (decision 25).
A move back happens after step 5 cannot move the second index, and after step 6 fails. The
message is then the step's own: "cannot write <name>" or "cannot write <path>". A `-o` file that
did not exist stays, empty, as in phase H.

**At the end, for exit code 0:**
1. **The index is finished:** the last blocks are written, the carried line is taken, and the
   index is finished (`hts_idx_finish` at the end-of-file block's address) with its metadata. If
   the index's flag is set, or this fails: "cannot index <path>", exit 2, with no end-of-file
   block.
2. **The file is closed:** the end-of-file block is written and the file closed, as today, with
   phase H's take-back if closing fails.
3. **The index is saved** (`hts_idx_save_as`) to the temporary file. htslib gets the name with
   `./` before a relative path (decision 7). Otherwise a name starting with a scheme htslib knows
   (`file:`, `data:`, `mem:`, ...; with libcurl, `http:` and the like) would not be opened as a
   local file.
4. **It is renamed** to `<path>.csi` or `.tbi` (`rename`: atomic, it replaces what is there; a
   symlink there is replaced, not followed).
5. **The duplicate descriptor** of the `-o` file is closed.

- **If step 3 or 4 fails,** the temporary file is removed and the end-of-file block is cut off
  again through the duplicate, as in phase H. The run gives "cannot write <path>.csi", exit 2.
- **If step 5 fails,** the index just renamed is removed, and the error is phase H's "cannot
  write <path>".

**For any other exit code,** no index is finished or saved, and the temporary file is removed.

**What each kind of run leaves (decision 14):**
- **refused before the open** (a usage error, `BadIdx`, a missing input, an input error before
  the first piece): the old `-o` file and the old indexes, untouched;
- **refused at the open, steps 1–6:** the same (a new `-o` file stays, empty), except an index
  whose move back failed, which stays as `<name>.old`;
- **once the open is done, a run that does not exit 0:** no index at either name. The temporary
  file is removed on a `-c e` stop, a driver error and "cannot index" (on the way out, or by an
  `atexit` handler). It stays, as a stray `<index>.tmp` that htslib never reads, only when the run
  is killed or Bend's runtime stops it. The runtime stops with `_exit` ("bend: out of memory",
  "bend: a Nat past ... 2^48-1"), so `atexit` does not run (decision 21);
- **on a normal exit:**
  - the index is there exactly when the run exits 0, and the `-o` file is then complete;
  - when the run exits 2 after the end-of-file block was written (the index could not be saved
    or renamed, or the close failed), the block is cut off again;
  - the exceptions are phase H's: the take-back itself fails, or the duplicate's close fails
    after the rename (the new index is then removed). In both, the file can keep the block with
    no index.

The index is written after the data, so htslib never warns that it is older.

### Errors (one line, exit 2)

New messages, each listed in law machine's comment, in the order a run meets them (decision 10):

| message | when |
|---|---|
| `error: -W needs a BGZF -o file` | `B.Args.index` is `BadIdx`; in `main`, before any input is opened |
| `error: no BGZF in this build <path>` (phase H) | any BGZF output in a build without libdeflate (`Io.out_set`, 2002) |
| `error: no index in this build <path>` | `-W` with BGZF output in a build with libdeflate and without htslib (`Io.out_index`, 2003) |
| `error: cannot index <path> (not a regular file)` | the `-o` file at its open, a FIFO with no reader too |
| `error: cannot write <path>.csi (it is the -o file)` | an index name is the `-o` file (symlink or hard link) |
| `error: output is an input <path>.csi` | an index name is an input or stderr's file |
| `error: cannot write <path>.csi` | an index name is a directory (itself or through a symlink) or cannot be looked at; the temporary file cannot be made; an old index cannot be renamed aside (all before anything is changed); the index cannot be saved or renamed |
| `error: cannot write <path>.tbi (htslib would read <stem>.csi first)` | TBI only: an older `<stem>.csi` exists (step 3), before anything is changed |
| `error: cannot index <path>` | exit code 0 only, after all messages: a line tabix refuses, for CSI a text that does not begin with `##fileformat=VCF`, or no memory for the index |

Each `.csi` message has a `.tbi` twin, naming the index name concerned. `<path>` is the `-o`
path, written as today (`\\`, `\n`, `\r` escaped). The prototype prints these messages itself
(`idx_die`). In step 2 they become codes that `main.bend`'s `out_fail` turns into messages:
2003–2005 for the three without a name, and one code per message and index name for the rest
(2006–2011), and 2012 for the `<stem>.csi` refusal (driver review 9; `main.bend`'s `ix_stem`
cuts `<stem>` from the escaped path as the driver cuts it).

### Effects and main.bend

- **New effect `Io.out_index(fmt, path)`:** fmt 1 is CSI, 2 is TBI; path is the index path's
  bytes. It is called once, after `Io.out_set` and before the first step. It answers 0, or 2003
  without htslib (only reached when `Io.out_set` accepted BGZF).
- **`Io.out_write` and `Io.out_close`** may answer the codes above as well.
- **main.bend:**
  - `main.n` computes `B.Args.index(xs)` next to `B.Args.output(xs)`;
  - `main.k` stops on `BadIdx`, before any input is opened;
  - the `Io` record carries the index path, for the messages;
  - `out_fail.go` gains the codes.

  About 60 lines.
- **io64.js:** `Io.out_index` answers 2003, so the JS build has no `-W`.
- **The thread count:** `-W` adds no thread. The compressor threads (16, or `--threads N`) do the
  parsing, and the writer pushes. The constructor's own parser (`io64_threads_of`) knows the
  eight words, so `-W` keeps `--threads N` (decision 12).

### build.sh

The draft is `data/tmp/index/build.diff`, copied below, and the new `tools/build_htslib.sh`
(decision 23).
- **It links htslib 1.24 statically, built without libcurl** (decision 17):
  - `tools/build_htslib.sh [PREFIX] [TARBALL]` builds and installs it, by default at
    `~/.local/opt/htslib-1.24-nocurl`: `./configure --disable-libcurl --disable-gcs --disable-s3
    --with-libdeflate`, from the 1.24 release tarball, checked by its SHA-256;
  - `build.sh` finds it with `pkg-config`, through `PKG_CONFIG_PATH` (by default that prefix's
    `lib/pkgconfig`), and links `$(pkg-config --variable=libdir htslib)/libhts.a` with
    `pkg-config --variable=static_libs htslib` (`-lpthread -lz -lm -lbz2 -llzma -ldeflate`),
    `-DFB_HTSLIB` and `pkg-config --cflags htslib`.
- **It refuses, before `bend` runs:**
  - no htslib 1.24 found;
  - a `libhts.a` whose `static_libs` name `-lcurl` (`~/.local/opt/htslib-1.24`, the libcurl
    build on this machine, is refused);
  - a `libhts.a` that does not define `tbx_parse1` and `hts_adjust_csi_settings` (`nm`).

  The message names the prefix, `tools/build_htslib.sh`, the three `--disable-*` flags and
  `FB_NO_HTSLIB=1`.
- **`FB_NO_HTSLIB=1 ./build.sh OUT`** builds with libdeflate and without htslib (1.78 MB), for the
  test of "no index in this build" (decision 10).
- **A plain `bend main.bend -o framebender` still builds,** without either library. There, BGZF
  output says "no BGZF in this build" first, `-W` included.
- **The binary grows from 1.8 MB to 5.7 MB** (6.1 MB with libcurl), with 8 shared objects
  loaded instead of 30. The prototype binary with indexing off ran in 2.84–3.01 s, the same as
  today's (step 1).

## Test plan (step 2)

`test/index.sh new_binary` (new), on:
- the edge cases;
- `test/gen_par.py`'s cases and the generated cases;
- chr22 and the scrambled file;
- the whole genome;
- the 1000 Genomes slice (`data/kg/sub.vcf`) and chr22 (`data/kg/chr22.vcf.gz`, records of
  14 KB).

Each case runs on the normal build and on the small-piece builds (300, 1,000 and 70,001 bytes).

**The differential rule** (decisions 18 and 22), for every case and setting:
1. run without `-W`;
2. if its code is not 0, each `-W` run must be that run exactly (stdout, stderr, exit code,
   output bytes), with no index at either name and no temporary file;
3. otherwise each format is judged on its own: CSI by `bcftools index`, TBI by `tabix -p vcf`, on
   a copy of that output:
   - if that tool refuses, the `-W` run gives the same stdout and stderr, then "cannot index
     <path>", exit 2, the output less its end-of-file block, and no index;
   - otherwise the index equals the tool's bytes, and the output bytes, stdout, stderr and exit
     code equal the run without `-W`;
   - either way, no temporary file is left.

A refusal of CSI alone cannot happen at `min_shift` 14: CSI holds at least 2^32, TBI 2^29. So a
CSI refusal with a TBI success is itself a failure of the test. `r2_oracle.sh` is the rule on
eight cases.

The end-of-file block is checked by its 28 bytes (`tail -c 28`). `bgzip -t` only warns when it
is missing, and exits 0.

**The settings:**
- `-c e` and `-c w`;
- `--threads` 1, 2, 3, 7, 16, 32 and 128;
- levels `-Oz`, `-Oz0`, `-Oz1`, `-Oz9`;
- every one of the eight spellings, each at three positions;
- `-o x.vcf.gz`, `-Ov -o x.vcf.gz`, `-o x.vcf.bgz` and `-o x.VCF.GZ`.

The index must also be the same at every `--threads`, checked directly, and stderr of failing runs
too.

**New edge cases:**
- **block boundaries:**
  - lines of 65,279, 65,280 and 65,281 bytes;
  - a record of 200 KB;
  - a header that ends exactly at a block's end, and a header longer than a block;
- **line forms:**
  - an output that ends without a LF;
  - CRLF lines;
  - a NUL byte in a body line;
- **no records:** a header with no records (with and without `##contig` lengths), and an empty
  output;
- **contigs:**
  - no `##contig` lines;
  - a `##contig` length past 2^32 (more CSI levels), and one past 2^41 (`min_shift` moves; no
    warning may appear);
  - records on many contigs, and contigs in an order unlike the header's;
- **lines tabix treats specially:**
  - body lines that start with `#` (tabix skips them);
  - out-of-scope records that pass unchanged, whose end tabix reads from INFO/END, SVLEN
    (`<DEL>`) or FORMAT/LEN (`<*>`);
  - `-c w` records with INFO/END below POS, and with POS 0. These are htslib warnings, so stderr
    must stay as without `-W`;
  - `END=` on every line (the lock).

**The "cannot index" cases** (each also refused by the reference tool on the same text):
- a leading-zero POS on an out-of-scope record, under `-c e` and `-c w`;
- the same with a `-c e` stop after it: the run without `-W` exactly (exit 1), and no index;
- `-Wtbi` with a POS past 2^29, and with an INFO/END past 2^29;
- CSI with no `##contig` length and a POS past 2^38;
- CSI with a short declared length and a POS past 2^32;
- each at `--threads` 1, 16 and 128: the same stderr.

**Queries.** For five regions on chr22 and on the whole genome, including regions that start or
end at a block boundary and at a 16 kb bin boundary:
- `tabix x.vcf.gz R` equals `bcftools view -H -r R` on a copy indexed by `bcftools index`;
- for SNV-only regions, it also equals an `awk` selection of the plain output by POS.

**Failures** (each: the message, the exit code, and the files as stated):
- **a `-c e` stop mid-file** (exit 1): no index at either name; old indexes at both names removed;
  the output as today;
- **a `.vcf.gz` input cut mid-file** ("bad BGZF", exit 2): no index, no temporary file;
- **Bend's runtime stops the run** (`bend: out of memory` under a cap; a POS past 2^48), exit 1:
  no index at either name, and a stray `<index>.tmp` (decision 21);
- **`-W` with stdout, `-o -`, `-o x.vcf`, `-Oz -o x.vcf`, `-o x` (no extension, no `-O`):** "-W
  needs a BGZF -o file", before any input is opened; no file created, nothing removed;
- **`-o` a FIFO** (no reader, under a timeout; and with a reader), **`/dev/stdout`, `/dev/null`:**
  "cannot index ... (not a regular file)"; nothing written or removed;
- **the order at the open (decisions 2 and 20), by failure injection** (`r2_fi.sh`'s shim, in
  `test/`): a failure at each of steps 1–7, on each index name, for `-W` and `-Wtbi`, from an old
  `-o` file and two old indexes with their own bytes. Expect the table in Round 3: steps 1–6
  change nothing unless a move back fails too (then that index stays as `<name>.old`), and step 7
  leaves `<name>.old` and a good index. The same with `renameat2` refusing `RENAME_NOREPLACE`
  (EINVAL, ENOSYS, EOPNOTSUPP: the link fallback), and with `link` refused too. Also:
  - a failure before the open (a missing FASTA): both old indexes remain;
  - `-o` a symlink to its own `.csi`: refused, nothing changed;
  - one index name a directory and the other a real index: the real one remains, the file
    unchanged;
  - a read-only `-o` in a writable directory: refused at the open, indexes remain;
  - a real sticky directory with an old index owned by another user (if the test can make one):
    refused at step 5, nothing changed;
- **saving fails**, injected with the same shim (the save's `open`, the final `rename`, either
  `close`; libc is still dynamic), and with `RLIMIT_FSIZE` set so that the data fits and the
  index does not:
  - each gives "cannot write <path>.csi";
  - the end-of-file block is taken back (by its bytes);
  - no temporary file is left;
  - a failing close of the duplicate removes the new index;
- **an index name that is the VCF, the FASTA, the `.fai` or stderr's file** (directly, through a
  hard link, through a symlink): "output is an input <path>.csi"; the input's md5 unchanged;
- **scheme-like paths (decision 7):** `-o file:x.vcf.gz`, `data:x.vcf.gz`, `mem:x.vcf.gz`,
  `http:/x.vcf.gz` (with a directory `http:`) and `chr1:1-1000.vcf.gz` write exactly the local
  files;
- **old indexes:**
  - `<out>.csi`, `<out>.tbi` and both are removed on success and on failure after the open;
  - a symlink at the index name is replaced, its target untouched;
  - a stray `<index>.tmp` is left alone;
  - `-W`, then the same run without `-W`: the old index stays, as the usage message says;
- **the new index's mode:** 0644 under umask 022, 0600 under 077. Its mtime is not older than the
  output's.

**Builds (decision 10):**
- **the libdeflate-only binary** (`FB_NO_HTSLIB=1 ./build.sh`): `-W -Oz` gives "no index in this
  build <path>" before the first step;
- **`bend main.bend -o fb_plain`:** `-W -Oz` gives "no BGZF in this build" (no "no index");
- **io64.js:** the same as the libdeflate-only binary for an index, if BGZF is there, else "no
  BGZF";
- **build.sh with no htslib 1.24, or one with libcurl, or a `libhts.a` without the two
  functions:** it stops with its message, before `bend` runs, and writes no binary;
- **`tools/build_htslib.sh`** with a wrong tarball: it stops on the SHA-256.

**Usage errors:** `-Wbai`, `-W=TBI`, `-W=`, `--write`, `--write-index=bai`, `--write-index==tbi`,
and `-W tbi` with a VCF path already given. Each must print the usage and exit 2.

**Gate:**
- `check.sh` through `test/bcheck.sh`;
- `test/same.sh`, `test/par.sh` and `test/out.sh` (unchanged output without `-W`);
- `test/threads.sh`, with each `-W` spelling on the line: the constructor's thread count.

**Timing** (under the bench lock, pinned, interleaved, ranges, peak RSS):
- whole genome `-Oz -W`, `-Oz -Wtbi` and `-Oz1 -W`;
- `--threads` 1, 4, 8, 16 and 32;
- against `bcftools norm -Oz -W --threads 16`, and framebender without `-W`;
- the same on the 1000 Genomes file, and on an `END=`-heavy genome (the lock).

## What the proofs and examples need, and the size of the work

**Examples:** the 32 above, already checked on the scratch copy.

**Proofs:**
1. **`proof_f_args.bend`:**
   - the 3 `Drv{...}` patterns gain a variable;
   - `Args.word`'s chain gains a branch: `w8` becomes the `-W` pick, and `w9` the VCF-path
     fallback;
   - each of the four walks along the chain (`kl`, `ab`, `inv`, `un` at lines 383, 420, 495, 564)
     gains one pick step, with a lemma for the `-W` state: `keep` unchanged, `PNone`, only `drv`
     changed. `un` is `{==}`, since `unthr` replaces `drv` with `Drv.none()`.

   About 100 lines changed or new.
2. **`proof_f_index.bend` (new):**
   - `idx_step`: from a state where an option is expected, a word with `idx_opt(x)` changes only
     `drv`, and in it only `Drv.idx`. `Args.wfmt(x)` is `Some` only for the eight words
     (`Q.str_eq_sound` on the `||` chain), and on each literal word `Args.word` evaluates;
   - `parse_idx`, as `parse_out`, with `[x]`;
   - law `index` from `FT.same_parse`, with `FO.texts_drop` for `o = [x]` (`[x] ++ post` is `x
     <> post` by evaluation);
   - law `index_sink`:
     - two states that differ only in `Drv.idx` stay so through `Args.go`: each later word
       sets the same field in both, or none;
     - `Args.sink` and `Drv.thr` ignore `Drv.idx`, by a case on `Drv`;
     - so `Args.sink.done` and `Args.thr.done` agree.

     That is the walk `same_parse` makes, over `drv`.
   - `index_ok`, as `output_ok` (`idx_done_ok`, `index_if`).

   About 400 lines.
3. **`PROOF.bend`** forwards `M.index` and `M.index_sink`.

No other proof matches on `Drv`. `Pend` gains no constructor, so `proof_b_bud_start.bend` and
`proof_b_drive_start.bend` do not change.

**Driver:**
- `io64.c`: about 450 lines (the scan with its lock, the push and carried lines, the finish and
  save, the open's order and checks, the temporary file, the removals, the rename and take-back,
  `io64_wfmt`);
- `main.bend`: about 60;
- `io64.js`: 5;
- `build.sh`: about 25 (drafted), and `tools/build_htslib.sh` (drafted).

**Docs:**
- README:
  - Run: `-W`, where the index goes, what refuses it, and that a run without `-W` leaves an old
    index (decision 15: htslib warns only when it is a second or more older than the file);
  - Results: the new timings;
  - the differences from bcftools;
- `docs/LAWS.md`: laws `index` and `index_sink`, and the trusted index writer under "What the laws
  do not cover". It says the process can exit 2 where the machine's code is 0, never that the
  exit code is unchanged;
- `docs/DEVELOPMENT.md`: `test/index.sh`, and htslib without libcurl as a build dependency;
- `NOTES.md`.

**Size:** about 1.5 to 2 days of agent work: one word, two laws, and a writer that is already
there.

## Scratch files (`data/tmp/index/`)

- `ex1.sh`–`ex3.sh`, `ex7.sh`: the bcftools experiments;
- `ex4.sh`–`ex6.sh`: the identity checks of the step 1 prototypes;
- `bench1.sh`–`bench6.sh` and their `.txt`: the timings (5: round 1's large identity runs and the
  stopped END-heavy genome; 6: round 1's lock timing);
- `r1_ident.sh`, `r1_cases.sh`, `r1_threads.sh` and their `.txt`: round 1's checks of the
  prototype (identity; T1–T6; the constructor's parser);
- `r2_fi.sh` (with `r2/fi_shim.c`), `r2_oracle.sh`, `r2_ident.sh`, `r2_cases.sh` and their
  `.txt`: round 2's checks (failure injection, the per-format oracle, and round 1's checks again
  on `fbp2`); `r2/rt/`: the runtime stop's stray `.tmp`;
- `proto/`:
  - `tidx.c`: B and A′, `tbx_index` on a file or stdin;
  - `pidx.c`: A's loop alone, on a file's text and block table;
  - `io64.c`, `idx_proto.h`, `build_proto.sh`: A inside the driver, enabled by
    `FB_PROTO_INDEX=csi:PATH`. `build_proto.sh OUT` builds it with the draft `build.sh` on the
    draft tree (whose parser takes `-W`): `data/tmp/index/fbp2` (round 2), `fbp2_nohts`
    (`FB_NO_HTSLIB=1`); `fbp1` is round 1's, `fbp` step 1's;
- `hts-nocurl/`, `build_hts.sh`: round 1's htslib build without libcurl (superseded by
  `~/.local/opt/htslib-1.24-nocurl`, decision 23);
- `draft/`: the tree with the law draft (and `ex_false.bend`, `ex_false2.bend`, `ex_false3.bend`),
  the draft `build.sh` and `tools/build_htslib.sh`; `types.diff`, `machine.diff`, `examples.diff`,
  `build.diff`; `check_examples.txt`, `check_false*.txt`;
- `r1_*.py`: the scripts that applied round 1 to the draft, the prototype and the scripts;
- `src/`: htslib and bcftools 1.24, unpacked, read only.

## Round 3's answers, and the open leads

Round 3 answered the questions of round 2:
- **the double fault:** the message stays as it is;
- **a failed removal of `.old`:** stays silent;
- **the rename:** the `link` fallback (decision 26);
- **the download script:** fine, with decision 27.

Open leads, not in phase J:
- removing old indexes on every BGZF rewrite without `-W`;
- framebender's slow INFO/END check (13× on chr22). The reviewers want it as its own phase,
  before gVCF users meet it.
