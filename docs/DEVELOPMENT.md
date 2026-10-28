# Development

## Build

```
bend main.bend -o framebender
```

Building needs Bend 2.0.39 and clang. Set `BEND_NO_TELEMETRY=1` to turn off Bend's telemetry. The
binary reads `+RTS --threads N` to set the number of threads.

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
runs at most two checks at once, each capped at 4 GB. A proof that evaluates a big number, such as
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

## Files

| files | role |
|---|---|
| `LAWS.bend`, `types.bend`, `run.bend`, `tan.bend` | science layer: definitions and laws |
| `protocol.bend`, `MACHINE.bend` | implementation contract: the machine law and the FASTA premise |
| `norm.bend`, `norm_line.bend`, `norm_run.bend` | the program, a state machine |
| `main.bend`, `io64.c`, `io64.js` | the trusted driver: file I/O and the `.fai` reader |
| `PROOF.bend`, `proof_*.bend` | the proofs; `PROOF.bend` proves every law by importing the rest |
| `examples.bend` | concrete cases checked by evaluation |
| `test/` | the bcftools comparison, the scrambler, edge cases, FASTA premise cases |
| `reviews/` | every law and driver review, with the responses |
| `refs/` | the sources the reviewers were given: the VCF 4.3 spec and the `bcftools norm` manual |
| `NOTES.md`, `notes/` | decisions, review history, proof notes, measurements |
| `notes/briefs/` | the briefs given to the agents that wrote the code and the proofs |

## Writing proofs

Read `notes/briefs/PROVING.md` before writing proofs. It covers Bend's proof syntax and the
patterns used here.

`NOTES.md`, "Where proofs got hard", has the lessons learned.
