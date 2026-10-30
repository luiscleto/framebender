Law and design review of a proposed change to framebender (read-only: do not modify, create or
delete files in the repository, and do not switch branches).

framebender is a VCF normalizer in Bend 2 whose behaviour is fixed by laws, and whose program is
proven to obey them. The science layer (`types.bend`, `LAWS.bend`, `run.bend`, `tan.bend`) says
what a run computes; the contract (`MACHINE.bend`, `protocol.bend`, `bytes_enc.bend`) says the
program computes exactly that (`law machine`, `law usage`, `law threads`, `law output`).
`docs/LAWS.md` explains them in plain terms. A trusted driver (`main.bend`, `io64.c`) reads and
writes files; it is not proven, and is tested instead. Phase H added `-o FILE` and
`-O v|z|z0..z9` (BGZF output, byte-identical to bgzip; `notes/compress.md`).

The proposal adds `-W` (`--write-index[=csi|tbi]`), as `bcftools norm -W` does: the driver
writes the CSI or TBI index of the BGZF output file, built on the fly with htslib 1.24's own code
(`tbx_parse1`, `hts_idx_push`, `hts_idx_save_as`), byte-identical to `bcftools index` and
`tabix -p vcf`. A new `law index` says the option never changes what the program writes.

The design, bcftools' behaviour (found by experiment and in its source), the drafted diff and
examples, the driver design, the test plan and the author's questions are in `notes/index.md` of
the worktree /home/luisc/Work/bend-projects/framebender-index (branch `index`); nothing tracked is
edited yet. The draft is applied to `data/tmp/index/draft/` (diffs in `data/tmp/index/*.diff`),
and a prototype driver is in `data/tmp/index/proto/`.

Review the law, the parser and the driver design (the final code comes after this review).
Questions:
1. Do `law index`, `law output`, `law machine` and `law usage` together say what a user needs:
   that `-W` never changes the text, only adds an index file? Is there a command line where a law
   holds while the program misbehaves, or where `-W` changes something no law covers? Is any
   approved law weakened (it must not be)?
2. The parser: the eight spellings, the glued forms, the last one counting, `-W` with `-O v`,
   stdout, `-o -`, a non-BGZF path; unambiguous, and the same `Cfg` as before for every command
   line accepted before? `index_ok` against `output_ok`.
3. The driver: on the fly with htslib against a second pass (`tbx_index_build3`); the virtual
   offsets; anything that could write an index that does not match the file (a block boundary,
   a failed run, `-c e` stopping mid-file, CRLF, a record spanning blocks, contigs out of order,
   positions past CSI/TBI limits), or leave a stale or partial index next to a file; the handling
   of `<out>.csi` and `<out>.tbi`; errors; memory and speed; a build without htslib.
4. Answer the author's seven questions at the end of `notes/index.md` with your own view.
5. The test plan: is it a fair substitute for a proof of the trusted part?

Use only the repository's files (`notes/index.md`, `notes/briefs/INDEX.md`, `notes/compress.md`,
the science and contract files, `examples.bend`, `docs/LAWS.md`, `io64.c`, `main.bend`,
`build.sh`) and `data/tmp/index/` (htslib's source is in `data/tmp/index/src`). You may run
`bend` checks, `bcftools`, `tabix` and the prototype only on copies under `/tmp`.

Report a numbered list: severity (blocker / should fix / minor), the exact place, why, and the
fix. Or say ACCEPT. Be brief. End with the full report as your final message.
