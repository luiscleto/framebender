# framebender on packed bytes (phase A: code, 2026-10-27)

Brief: `notes/briefs/BYTES.md`. Contract: `protocol.bend`, `MACHINE.bend`, `bytes_enc.bend`
(revised by the lead in two review rounds while this was written; the code meets the round-2
contract: well-formed output buffers, reads of at most 2^31 letters, steps that write less than
2^31 bytes).

Files changed or added: `norm.bend` (rewritten), `norm_run.bend` (rewritten), `norm_fast.bend`
(new), `norm_line.bend` (the reference answer is a `D.Bytes`), `main.bend`, `io64.c`, `io64.js`,
`../lawful-bytes/fast.bend` (new), `../lawful-bytes/test/fast_spot.bend` (new). The science layer,
the contract, `../lawful-bytes/bytes.bend` and `../lawful-fields` are untouched.

## Result

All timings: `nice -n 19`, a timeout, nothing else running (`pgrep -x bend` empty before and
after), back to back, output to `data/tmp`, wall clock.

| input | main's binary | this branch, default threads | `+RTS --threads 1` | bcftools 1.24 |
|---|---|---|---|---|
| chr22 (50,284 records) | 5.11 s | 0.141 0.146 0.155 s | 0.128 0.139 0.146 s | 0.131 0.131 0.132 s |
| `data/scr.vcf` (20,739, all but 4 rewritten) | 7.34 s | 4.80 4.92 s | 4.81 5.00 s | 0.075 s |
| whole genome (4,048,342) | ~590 s (pass 3) | 6.90 8.90 s | 8.35 8.43 s | 8.64 8.78 s |

Earlier rounds of the whole genome on the same build family spread from 7.1 to 9.8 s, with
bcftools at 7.4 to 9.2 s in the same rounds. The spread follows the disk: about 2.8 GB of output is
written through dm-crypt. The binary runs one sequential computation, so the thread count does
not matter.

Correctness (final build):

- `test/compare.sh data/chr22.fa data/hg002.chr22.vcf`: 0 differing records.
- `test/compare.sh data/chr22.fa data/scr.vcf`: 0.
- `test/compare.sh test/edge/ref.fa test/edge/sorted.vcf`: 1 (the `<DEL>` record).
- `TMPDIR=data/tmp test/compare.sh data/hg38.fa data/hg002.all.vcf`: exit codes 0 and 0, 0
  differing records. The outputs were deleted afterwards.
- stdout, stderr and the exit code are byte-identical to `main`'s binary (`data/tmp/fb_main`,
  built from a worktree of `main` at bba5bb7) on:
  - every `test/edge/*.vcf`, chr22 and `data/scr.vcf`, under `-c e` and `-c w` (30 files);
  - 22 more inputs made for the byte path (`data/tmp/gen_edge.py`, not committed). They cover:
    - END entries: right, wrong, bare, `ENDX`/`XEND`, `END` inside values;
    - empty INFO, lower case, leading zeros, duplicate alleles, multi-allelic records, `*`,
      `<DEL>`, N, IUPAC in REF, REF mismatch;
    - 8 fields, and 8 fields ending in CR;
    - CRLF files, some lines with CR, files without a final LF;
    - POS 0 and POS 99999999999, short lines, a blank line, an empty or unknown CHROM;
    - a CHROM change, UNSORTED, files with only a header, with no header, and empty;
    - a 4 MB line (longer than a piece), and 20,000 records in CRLF;
  - `-w 1`, `-w 5` and `-w 300` on six of them (scr, mix, CRLF, unsorted, in.vcf, 20,000
    records), under `-c e` and `-c w`;
  - all of the above again with a test build whose step ends at 100 KB of output and whose FASTA
    reads go in 4 KB parts. This exercises the code paths that only very large inputs reach.
- `bend main.bend --check-only`: only the expected report (51 defs rely on unsafe or foreign
  code). `bend MACHINE.bend --check-only`: only its 15 TODOs (the laws whose proofs are pending).
- `../lawful-bytes`: `bend test/fast_spot.bend` is all True. It compares `fast.bend` with
  `bytes.bend` on every range of a 22-byte buffer: `find` for 3 values, `find2`, and `append` at
  6 destination lengths × 12 starts × 5 lengths.

## Changes, with chr22 before and after

| step | change | chr22 | whole genome |
|---|---|---|---|
| 0 | main's binary | 5.11 s | ~590 s |
| b1 | the machine on packed bytes: fast path on the bytes, the output buffer as the sorting buffer, the reference cached as one window, 4 MB pieces read into blocks (design below) | 0.18-0.27 s | 12.06 s |
| b2 | reads start 64 K letters earlier (`margin`): scrambled records just before the window no longer miss | 0.19-0.21 s | |
| b3 | `Io.fa_read` tests a line's letters in one vectorizable pass and copies them with `memcpy`, not a byte at a time; the output buffer is grown once per piece, to the piece's size (`NR.reserve`); 3.5 MB pieces, so a piece with its carried bytes fits a 4 MB block | 0.125-0.154 s | 10.01 s |
| b4 | the buffer started at a step's end is sized to the carried bytes plus the input still to handle (it was the full capacity, zero-filled at every step: 2.3 s of 8.8 s); the C effects zero only the padding; reads look 16 M letters ahead (659 → about 170 reads) | 0.17-0.19 s (noise) | 7.11 7.39 s |
| b5 | contract round 1-2: FASTA reads in 16 MiB parts with a 64-bit span; a step ends (`Ask{[]}`) once it wrote 2^30 bytes; reads capped at 2^31 letters; an empty CHROM never takes the fast path | 0.13-0.16 s | 6.90-8.90 s |

Where the time goes now (gprof, `--threads 1`, whole genome, b4; user time 4.5 s of about 8 s
wall, the rest is the kernel reading 2.8 + 2.7 GB and writing 2.8 GB):
- the per-record fast path (`advance`, everything inlined): 1.5 s, about 360 ns a record;
- `Io.fa_read`: 0.8 s;
- copying records to the output (`fast.append`): 0.55 s;
- the sorting buffer's lists: about 0.3 s.

scr (slow path for almost every record) spends 60% in reference counting of shared Strings
(`term_drop`, `span_fade`) inside the String judge and `Rec.rebuild`. That is the old code, unchanged.

## Design

**Input.** The machine keeps a list of sources `Src{b, at}`: buffers whose lines from offset `at`
on are not handled yet, plus `pend`, the end of a line not complete yet.

- A piece (`P.Chunk{b}`) is read in place:
  - if `pend` is empty, it is the new source;
  - otherwise the first LF of `b` is found, and `pend ++ b[0..lf]` (one line) becomes a source
    before `Src{b, lf+1}`;
  - a piece with no LF goes to the end of `pend`.
- When a source holds no more complete lines, its rest moves to `pend`.
- At the end of the file, a non-empty `pend` gets an LF and is the last line. Its text is then what
  `B.Text.last` gives (`p ++ "\n"`, also when p ends with CR).

**Fast path (most records).** A body line in the current CHROM run (`norm_fast.bend` and
`fast.*` in `norm.bend`):

1. Its first 8 fields are cut with `find2(TAB, LF)` (`NF.cut`). INFO's end is followed by a search
   for the line's LF.
2. POS must be 1-9 digits with no leading zero.
3. REF and every ALT (up to 16) must be upper-case A, C, G, T or N.
4. The alleles must not all end with the same base, must not all start with the same base while
   all have 2 or more, and no two may be equal.
5. INFO must have no `END` entry: at each `E`, the test is whether it starts an entry with key
   `END`.
6. If INFO is the last field, the line must not end in CR.
7. CHROM must be non-empty and equal to the run's bytes (`cb`) and to the cached window's.
8. The window must hold REF and REF must lie within the contig. REF must equal the window's
   letters, case aside (`(x ^ y) & 0xDF == 0`).

The record's bytes then go to the output unchanged, and its item into the sorting buffer.

- If the window does not hold the record, the machine asks for `[POS-1-64K, POS-1+len(REF)+16M)`
  (`Want`), and handles the line again once the answer comes.
- Any other doubt sends the line to the slow path.

**Slow path (header lines, and any doubt).** The line's text is decoded (`BY.to_list` and `chars`)
and handled by the existing String code: `J.pfs`, `J.judge_fs`, `J.fast`, `R.head_line`, the run's
rules.

- Reference reads go through the cached window first (`serve`). It answers a read `(c, a, b)` when
  the last answer was for c, from `A <= a` up to `B` with `min(b, clen) <= min(B, clen)`, by
  slicing it.
- Otherwise the machine asks for `[a - 64K, max(b, a + 16M))`, capped at 2^31 letters.
- The window grows back as before (`grow`), in one self-recursive loop (`slow.go`).

**The run (`norm_run.bend`).** `Run` is `run.bend`'s `RunSt` on bytes:

- `ob` holds the bytes written this step (its first `ow`), then the texts of the buffered items, in
  buffer order. Writing ready items only moves `ow`.
- The buffer is `front ++ reverse(back)`. An item whose key is not below the buffer's largest is
  pushed on `back`, and its text appended to `ob`. Any other item is inserted in a single sorted
  list (`mid`), and its text inserted into `ob`'s tail.
- `last` keeps no text. An item's POS as written is `None` for fast items (it is `Nat.show(key)`).
- At a step's end, `ob[0..ow)` is the step's output (`NR.take`). The buffered texts are copied
  into a new buffer sized to them plus the input still to handle.

**Steps.** A step ends:

- with `More` (no complete line left);
- with `Ask{[req]}` (one read);
- with `Finish{code}`;
- with `Ask{[]}`, once the step wrote 2^30 bytes (`Yield`). This keeps every output buffer within
  2^31 bytes. The empty answer keeps the cached window (`set_win`: nothing was asked).

## The refinement argument (fast path vs the String path)

Let L be the line's bytes `s .. lf` (lf its LF) and `l = line(text(s, lf - s))` its `B.Line`. Claim:
when the fast path takes L (`WHit`), the run state after `NR.fast_done` is the one the slow path
reaches on `l`. That is `J.fast(Some w, J.pfs(body), body) == Same`, then `same_done`, with
`J.fast`'s window equal to the cached answer w. This is the `J.same` pattern of `notes/fast.md`.

1. **Fields.** `e0 .. e6` are the first 7 TABs from s and `e7` the next TAB or LF, all before the
   first LF lf (find2 stops at LF). If `e7 = lf`, the byte before lf is not CR (tested). So the
   body (L without LF, without a final CR) split at TAB has `[s,e0), [e0+1,e1), …, [e6+1,e7)` as
   its fields 0-7. `J.c7` gives `Got{f0..f6, r}` with these, and `J.pfs` keeps INFO as `""`,
   because `noend` holds (5).
2. **Not malformed.** There are 8 or more fields. f0 is non-empty (`s < e0`). `Pos.read(f1)` is
   `Some v` (2). REF is letters (3). No ALT allele is empty (3).
3. **In scope.** Every ALT allele is letters (3).
4. **POS.** `Nat.show(v) == f1`: 1-9 digits, the first not `0`. Also `v >= 1`, so not BAD_POS.
5. **INFO.** An entry has key END iff it starts with `END` followed by `=`, `;` or INFO's end. Such
   an entry starts at INFO's start or after `;`, and every one begins with an `E`. So `noend`
   finding none means `Info.ends(INFO) = []`, and `end_ok` holds (`J.noend_scan` already relates
   this to the String scan).
6. **Alleles.** `Allele.read` and `Alleles.read` are `Some`, and `Allele.show` and the joined
   `Alleles.show` give f3 and f4 back (upper case ACGTN). `Alleles.distinct` holds (byte equality
   is base equality on upper-case ACGTN).
7. **Normal form.** `lasts_eq` is false, so `right` stops at once (`AStop`, needing no base). Not
   (`firsts_eq` and `all_long`), so `left` stops at once. So `var_in(off, bases, v) == Some v`, and
   `same_var` and `same.text` hold.
8. **REF check.** The window is a truthful answer for CHROM (the cache keeps `truth`'s answers,
   and its chrom bytes equal CHROM). It covers `[POS-1, POS-1+len)` and `POS-1+len <= clen`
   (`fits`, `covered`). Each letter equals REF's byte up to case. With REF upper-case ACGTN,
   `Base.of_fasta` of the letter is REF's base, so `ref_check = Some True`.
9. By 1-8, `J.fast(Some w, fs, body) = Same`. The slow path would read with its own window,
   `[POS-1-back, POS-1+len)`, but the result does not depend on the window once it is `Some` (the
   existing machine proof's TL accepts any truthful answer).
10. **The run.** CHROM equals `cb`, the bytes of `cur`, so `keyed` takes `same_run`. `fast_done`
    does exactly what `NR.same_done` does: bump(F,F,F), then `same_run` with
    `Ck{POS, n, None, lf+1-s}`. Here `None` stands for `Nat.show(POS) = f1` (4), and the item's
    text is L's bytes, which is `Line.text(l)` (body ++ term, with CR in the term or the body as
    it came).

`NR.Run` refines `R.RunSt`, with `blank_st` for `last` as in pass 2. The full mapping is in
`norm_run.bend`'s header comment.

## The trusted driver (main.bend, io64.c)

What it does, exactly:

- **Pieces.** `Io.read_block(file, 3670016)` reads from the VCF's position until 3.5 MiB are read
  or the file ends (looping over short reads, retrying `EINTR`). The bytes go straight into a heap
  block of the smallest depth d with `4 * 2^d >= n`, and every byte past n is set to 0. That is
  `E.enc` of the piece: `D.Bytes{n, block}`. A short last piece is moved (`memcpy`) to its
  smaller block. n = 0 means the end of the file (`P.Eof`). A read error gives
  `error: cannot read <vcf>`.
- **Reference reads.** For `Req{c, a, b}`, the driver looks c up in the `.fai` (unchanged Bend
  code): Unknown if absent. Otherwise, with `a2 = min(a, n)` and `b2 = min(max(a2, b), n)`:
  - if `a2 = b2`, the answer is `Known{n, a2, D.Bytes{0, [0]}}` (enc of "");
  - if `b2 - a2 > 2^31`, it stops with `FASTA read too large` (the program never asks for that);
  - otherwise `Io.fa_read` reads the bytes from `fai_at(a2)` to `fai_at(b2)` (64-bit offset and
    span) in parts of 16 MiB with `pread`. It checks each byte against the layout: LF only at
    column lw-1; CR only at column lb when lw = lb+2; any other byte only below column lb and
    not a space or tab. A run of letters is checked in one loop, then copied with `memcpy`; on any
    doubt the bytes go one at a time, by the same rule. The letters are packed as enc (padding
    zeroed).
  - Code 1 (a misplaced byte) gives `unsupported FASTA`. Code 2 (letter count not `b2 - a2`) gives
    `.fai index does not match`.
  - The answers are given in order.
- **Output.** `Io.write_block(1, len, block)` writes the block's first len bytes to fd 1, all of
  them (looping over short writes, retrying `EINTR`), and frees the block. A failure gives
  `cannot write`. Messages are written as before (`Io.write_fd`, a list of bytes).
- **Unchanged:** argument handling, `.fai` parsing and checks, errors and exit codes.
- **Removed:** `Io.pread_full`, `Io.read_str`, `Io.write_str`, and the Bend `letters`/`fits`
  loops (now in `Io.fa_read`).
- **Runtime internals the C uses:** `heap_alloc`, `heap_free`, `blk_wcls`, `term_blk`,
  `blk_loc`, `blk_cls`, `blk_free`, `io_tup`, `io_done`, `io_fail`, `io_hand`, `io_hand_v`.
  Bend 2.0.39 has no ABI promise.
- `CID()` cannot name an imported constructor (`D.Bytes`), so the effects answer `(n, block)` and
  Bend wraps them in `D.Bytes`.

## lawful-bytes bodies replaced

`bytes.bend` is unchanged (the lead's later instruction). The word-at-a-time versions are in
`../lawful-bytes/fast.bend`, with the same names and signatures:

- `find(b, from, to, c)`: the zero-byte trick on `w ^ c*0x01010101`, the first word masked below
  `from`, the lowest flagged byte (`bidx`), capped at `to`. Words are read past `to` (wrapping
  inside the block).
- `find2(b, from, to, c1, c2)`: the same, on the OR of the two masks. The lowest flag of each mask
  is exact, so the lowest of the OR is.
- `append(dst, src, s, n)`:
  - bytes up to dst's next word boundary go through `bytes.bend`'s `append`;
  - the rest go a word at a time, each word `(lo >> sh) | (hi << (32 - sh))`;
  - it writes up to 3 bytes past the new length, which stays inside the block when `len + n` is
    within capacity (the law's hypothesis; framebender keeps 8 bytes to spare).

Proof needs for these: the one-way zero-byte lemma (no flag below the first zero byte), and the
shifted-word lemma for `append` (`view` only reads `len` bytes, so the bytes past it are free).

## What the proofs will need

1. `fast.bend` equal to `bytes.bend` (above).
2. The fast-path lemmas of the refinement argument, one per test: `NF.cut` against `String.split`
   / `J.c7`, `NF.num` against `Pos.read`/`Nat.show`, `NF.bases` and `alleles` against
   `Allele.read`, `distinct` and `var_in`'s first steps, `noend` against `Info.ends`, `refeq`
   against `ref_check`. Then `fast_done = same_done` on the decoded line.
3. The decoding: `text(b, s, n)` is `E.text` of the range; `J.bases(raw)` is
   `Bases.of_fasta(E.text(raw))`.
4. The input: sources, `pend`, the joined first line and the EOF line give `Text.lines` of
   `concat(cs)` (the new `proof_machine_lines`).
5. The run: `NR.Run` refines `R.RunSt`: `ob`/`ow` for out and the buffered texts; `front`/`back`
   for buf; `mid`'s insertion as `R.insert`; `flush` as flush of `take_ready` (only the first item
   can break); `take` keeps the meaning.
6. The cache: `serve`'s slice of `truth(c, A, B)` is `truth(c, a, b)` when it answers. `win_of`
   keeps the answer to the read asked last; `Ask{[]}` keeps it.
7. Contract side conditions:
   - every output buffer is well formed (perfect blocks from `Array.new`/`grow`, depth at most 29,
     `ow` within capacity);
   - every read asks for at most 2^31 letters (`Req.of`'s cap; `fast.need` asks
     `64K + len(REF) + 16M`);
   - every step writes less than 2^31 bytes (Yield at 2^30, plus at most one line).
8. Termination and budgets: `slow.go` is bounded by 64 tries; the pump's fuel is `4 * (2^32 - 1)`
   steps (a piece is at most 2^31 bytes); the read and step counts must fit `bound`.

## Limits (cases the law covers that this code may not meet)

- **Lines longer than about 2^30 bytes.** `pend` or one step's output could pass 2^31 bytes.
  No VCF has such lines, but the law quantifies over every input.
- **Contigs longer than 2^31 letters.** A slow record that must read back to such a contig's start
  needs a window larger than a read may ask for; the line is asked for again without end. Such
  contigs do not exist in practice (`P.Fasta.plain` does not exclude them).
- **POS of 2^31 or more.** The cache's U32 fields (`offu`, `clenu`) disable the fast path, so
  such records take the slow path: correct, but slow.
