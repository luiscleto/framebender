Law review of a proposed change to framebender (read-only: do not modify, create or delete files
in the repository, and do not switch branches).

framebender is a VCF normalizer in Bend 2 whose behaviour is fixed by laws, and whose program is
proven to obey them. The science layer (`types.bend`, `LAWS.bend`, `run.bend`, `tan.bend`) says
what a run computes; the contract (`MACHINE.bend`, `protocol.bend`, `bytes_enc.bend`) says the
program computes exactly that (`law machine`, `law usage`, `law threads`). `docs/LAWS.md`
explains them in plain terms. A trusted driver (`main.bend`, `io64.c`) does the file reading and
writing; it is not proven, and gets its own driver review.

The proposal adds compressed output, as `bcftools norm -o FILE -O z` does: `-o FILE` (where to
write) and `-O v|z|z0..z9` (plain or bgzip/BGZF, with a level; also glued, `-Oz9`). The design
and the drafted diff are in `notes/compress.md` (the repository is the worktree at
/home/luisc/Work/bend-projects/framebender-gz, branch `gz`); nothing tracked is edited yet. The
draft is also applied to a scratch copy in `data/tmp/gz/draft/` with diffs there. In short:
- `B.Args.parse` (`types.bend`) accepts `-o FILE` and `-O T` among the options, the last one of
  each counting; the type follows `-o`'s extension (`.vcf` plain, `.vcf.gz`/`.vcf.bgz` BGZF) over
  `-O`, as bcftools 1.24 does; BCF is a usage error. They are not recorded in the header's command
  line (as `--threads` is not), and `B.Args.output` gives the driver a `Sink{file, z, level}`.
- A new `law output` in `MACHINE.bend`, in the style of `law threads`: adding one output option
  where an option is expected gives the same `launch` (paths, output bytes, messages, exit code).
- The driver compresses the output bytes in BGZF blocks, as bgzip does, in parallel with
  libdeflate, so the file is byte-identical to `framebender ... | bgzip -l L`. This part stays
  trusted and is tested against bgzip, tabix and bcftools instead.

Review the law and the design, not the code (the code and proofs come after this review).
Questions:
1. Do `law output`, `law machine` and `law usage` together say what a user needs: that the output
   options can never change the text, only how and where it is written? Is there a command line
   where they change something the laws do not cover, or where a law could hold while the program
   misbehaves (for example a statement that is true for a reason unrelated to output)? Is what
   stays trusted stated plainly, and is the test plan a fair substitute for a proof there?
2. The parser: is the new grammar unambiguous, and the same as before for every command line that
   was accepted before (byte-for-byte the same `Cfg`, including `Opts.args`)? Check the drafted
   examples, including `-o` as the value of `-f`, `-o` naming an input, missing values, glued
   forms, repeated options and the extension rule.
3. Answer the author's five questions at the end of `notes/compress.md` with your own view: the
   extension winning over `-O`; leaving the options out of the header; completing the BGZF file
   when a run stops with an error; the default level (6, or 1 for speed); `-o` refusing an input.
4. The driver design (section "The driver"): anything that could make a file that decompresses to
   something other than the output bytes, or a wrong file left behind (partial output, a failed
   run, `-o` naming an input or the same file twice, a full disk, signals), or a large memory or
   speed cost.
5. Anything a scientist reviewing these laws would find unclear, or a simpler statement.

Use only the repository's files (`notes/compress.md`, `notes/briefs/COMPRESS.md`, `types.bend`,
`MACHINE.bend`, `LAWS.bend`, `examples.bend`, `docs/LAWS.md`, `io64.c`, `main.bend`,
`notes/threads.md` for the `--threads` precedent) and `data/tmp/gz/draft/`. You may run `bend`
checks, `bcftools`, `bgzip` and `tabix` only on copies under `/tmp`.

Report a numbered list: severity (blocker / should fix / minor), the exact place, why, and the
fix. Or say ACCEPT. Be brief. End with the full report as your final message.
