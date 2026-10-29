# Development

## Build

```
./build.sh
```

Building needs Bend 2.0.39, clang and libdeflate (headers and library: the `libdeflate` package on
Arch, `libdeflate-dev` on Debian and Ubuntu, `libdeflate` in Homebrew). `build.sh` builds in two
steps: `bend main.bend -o framebender.c` writes the program as C (with the driver's effects from
`io64.c`), then `clang -std=c11 -O3 -DFB_LIBDEFLATE ... -ldeflate` compiles it, as `bend -o` would
plus libdeflate, which reads BGZF (`.vcf.gz`) input. `./build.sh out` writes the binary to `out`.

`bend main.bend -o framebender` still builds in one step, without libdeflate. That binary reads
plain VCF only and stops on a `.vcf.gz` with `error: no BGZF in this build <path>`.

Set `BEND_NO_TELEMETRY=1` to turn off Bend's telemetry (`build.sh` sets it). `--threads N` sets
Bend's worker threads too (`io64.c` puts `--threads N` before `BENDRTS` before `main`); the binary
still reads `BENDRTS="--threads M"` and `+RTS --threads M -RTS`, which win. A build with
`-DFB_NO_RTS_THREADS` leaves the runtime's threads alone.

## Check the proofs

```
./check.sh
```

`check.sh` runs these in order:

1. checks the examples (`examples.bend`);
2. type-checks the driver;
3. checks every proof in `PROOF.bend` with `bend`;
4. checks them again with Bend's Lean-proven kernel (`--verdict`, which needs Lean via elan in
   `~/.elan`).

It prints `ALL PROOFS CHECK` twice when everything holds. A change to the code is acceptable when
`check.sh` passes; a change to the science layer needs a new law review (`refs/REVIEW_PROMPT.md`).

To check one proof file while working, use `test/bcheck.sh file.bend [--check-only|--verdict]`. It
runs at most two checks at once, each capped at 4 GB, with a 64 MB stack. A proof that evaluates a big number, such as
`Nat.pow(2n, 29n)` closed by `{==}`, builds it in unary and can otherwise fill the machine's memory.

## Compare with bcftools

```
test/compare.sh ref.fa in.vcf
```

The script runs both tools with `-c w` and counts the records that differ. Before comparing it
upper-cases REF and ALT, and pads sample columns to the FORMAT length the way htslib does on
output.

- Set `BCFTOOLS` and `FRAMEBENDER` to choose the binaries.
- For large inputs, point `TMPDIR` at a disk with room for both outputs, about twice the input
  size.

Expected results:

| input | differing records |
|---|---|
| `data/hg002.chr22.vcf` | 0 |
| the scrambled file | 0 |
| `test/edge/sorted.vcf` | 1, the `<DEL>` record bcftools realigns |

`test/scramble.py ref.fa in.vcf copies seed > out.vcf` makes a stress test. It rewrites each indel
at random equivalent positions, with random padding and case.

Test data (not committed): UCSC hg38 (`chr22.fa.gz` or the whole `hg38.fa`), and the GIAB HG002
NISTv4.2.1 GRCh38 benchmark VCF.

## Benchmarks

Time with `nice -n 19` and a `timeout`, one benchmark at a time, before/after runs back to back.
`NOTES.md` (Q5) and `notes/fast.md` record every measurement and where the time goes.

## Compare with the previous build

`test/same.sh new_binary [old_binary]` runs both binaries on every edge case, chr22, the scrambled
set and the generated inputs (`test/gen_edge.py`, `test/gen_rw.py`, run first from the repository
root), under `-c e`, `-c w` and several `-w`, and reports any difference in stdout, stderr or exit
code. Use it after any change to the implementation, together with the gate.

`test/threads.sh new_binary old_binary` checks law `threads` on these cases: `new_binary` with
`--threads N` (1 to 128, at three positions) against `old_binary` without it, then the usage errors
of `--threads` and the threads a run starts.

`test/par.sh new_binary [old_binary]` does the same on the batch-boundary cases of the parallel
machine (`python3 test/gen_par.py`, then `samtools faidx data/tmp/par/par.fa`): a CHROM change at
a piece boundary, a record moving left across one, unsorted input, `-c e` stopping mid-batch,
files shorter than a batch. Run both on builds with small pieces too: `main.bend` sets the piece
size (3670016 bytes); a test build replaces `3670016ull` in the generated C with 300, 1000 or
70001.

## Files

| files | role |
|---|---|
| `LAWS.bend`, `types.bend`, `run.bend`, `tan.bend` | science layer: definitions and laws |
| `protocol.bend`, `MACHINE.bend`, `bytes_enc.bend` | implementation contract: the machine law, the FASTA premise, and how bytes encode the spec's text |
| `norm.bend` | the program: pieces judged in parallel in batches of 16 (`../lawful-halves`) and spliced in order, falling back to the sequential machine |
| `norm_seq.bend`, `norm_fast.bend`, `norm_line.bend`, `norm_run.bend`, `norm_fix.bend` | the sequential machine on packed bytes (`../lawful-*`) |
| `main.bend`, `io64.c`, `io64.js` | the trusted driver: file I/O and the `.fai` reader |
| `build.sh` | the two-step build with libdeflate |
| `PROOF.bend`, `proof_*.bend` | the proofs; `PROOF.bend` proves every law by importing the rest (`proof_b_*`: the bytes machine, `proof_c_*`: rewritten records, `proof_e_*`: the parallel machine; notes in `notes/*proofs*.md`) |
| `examples.bend`, `examples_machine.bend` | concrete cases checked by evaluation; the machine's cases are outside the gate (they pass 4 GB in the checker) |
| `test/` | the bcftools comparison, the scrambler, edge cases, FASTA premise cases |
| `reviews/` | every law and driver review, with the responses |
| `refs/` | the sources the reviewers were given: the VCF 4.3 spec and the `bcftools norm` manual |
| `NOTES.md`, `notes/` | decisions, review history, proof notes, measurements |
| `notes/briefs/` | the briefs given to the agents that wrote the code and the proofs |

## Writing proofs

Read `notes/briefs/PROVING.md` before writing proofs. It covers Bend's proof syntax and the
patterns used here.

`NOTES.md`, "Where proofs got hard", has the lessons learned.
