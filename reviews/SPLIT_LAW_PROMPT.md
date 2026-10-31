Law review of a proposed change to framebender (read-only: do not modify, create or delete files
in the repository, and do not switch branches).

framebender is a VCF normalizer in Bend 2 whose behaviour is fixed by laws, and whose program is
proven to obey them. The science layer (`types.bend`, `LAWS.bend`, `run.bend`, `tan.bend`) says
what a run computes; the contract (`MACHINE.bend`, `protocol.bend`, `bytes_enc.bend`) says the
program computes exactly that (`law machine`, `law usage`, `law threads`, `law output`).
`docs/LAWS.md` explains them in plain terms. The laws are meant to be approved by geneticists
who do not read code, so each law needs a plain statement that is true and complete.

The proposal adds splitting of multiallelic records, as `bcftools norm -m -any -f ref.fa` does:
a record with several ALTs becomes one record per ALT, each then normalized and sorted. Genotypes
(FORMAT/GT) are rewritten for each ALT, and INFO and FORMAT values are cut by their header
`Number` (A, R, G). Where bcftools 1.24 guesses, drops data or crashes, the proposal refuses the
line instead (new problem codes `UNDEFINED_TAG`, `BAD_COUNT`, `BAD_GT`).

The design, bcftools' behaviour (found by experiment, 32 rows with commands), the drafted diff
(Appendix A) and examples (Appendix B) are in `notes/split.md` of the worktree
/home/luisc/Work/bend-projects/framebender-split (branch `split`); nothing tracked is edited yet.
The draft is applied to a scratch copy in `data/tmp/split/draft/` (it type-checks; its examples
evaluate), and the experiments are in `data/tmp/split/` (`run.sh`, `cases/`, `out/`).

Review the laws and the design, not the code (the code and proofs come after this review).
Questions:
1. Do the 13 new laws, with the changed `run`, `items` and the existing laws, say what a user and
   a geneticist need: that each record written is one ALT of the input, normalized, with its
   genotypes and per-allele values correctly assigned, and nothing else changed? Is there an
   input where a law holds while the output is wrong, a law true for an unrelated reason, or a
   gap (a field or case no law speaks about)? Is any approved law weakened (it must not be)?
2. The genotype rule (`split_gt`, `split_phase`) and the value rules (`split_info_values`,
   `split_format_values`, Number G for diploid and haploid samples): correct against the VCF 4.3
   specification and against bcftools' table in `notes/split.md`? Check the G index formula and
   the haploid case. Is anything stated in indexes that a geneticist cannot check?
3. The differences from bcftools (the section "Where framebender differs"): is each refusal
   justified, or would it reject common real files (for example INFO tags without header lines,
   or `AD=.`)? Are there differences the author missed?
4. The parser: `-m -any`, `-m -both`, `-m -`, the glued forms, `--multi-overlaps 0|.`, and the
   usage errors for `+` (joining), `-snps`, `-indels`, `--keep-sum`. Unambiguous, and the same
   `Cfg` as before for every command line accepted before? What `law threads` and `law output`
   need at the two new waiting states.
5. Answer the author's five questions at the end of the design (the default of
   `--multi-overlaps`; `-c w` on a line that cannot be split; `UNDEFINED_TAG`; `biallelic_run`;
   the wording of the value laws) with your own view.
6. The plan: the String path for split lines, the proof plan and its size, the tests (identity
   with bcftools, generated cases, cohort speed). Anything that makes the plan unlikely to give a
   fast, correct tool.

Use only the repository's files (`notes/split.md`, `notes/briefs/SPLIT.md`, the science and
contract files, `examples.bend`, `docs/LAWS.md`, `NOTES.md`) and `data/tmp/split/`. You may run
`bend` checks and `bcftools` only on copies under `/tmp`.

Report a numbered list: severity (blocker / should fix / minor), the exact place, why, and the
fix. Or say ACCEPT. Be brief. End with the full report as your final message.
