Law review of a proposed change to framebender (read-only: do not modify, create or delete files
in the repository, and do not switch branches).

framebender is a VCF normalizer in Bend 2 whose behaviour is fixed by laws, and whose program is
proven to obey them. The science layer (`types.bend`, `LAWS.bend`, `run.bend`, `tan.bend`) says
what a run computes; the contract (`MACHINE.bend`, `protocol.bend`, `bytes_enc.bend`) says the
program computes exactly that (`law machine`, `law usage`). `docs/LAWS.md` explains both in plain
terms. The program judges batches of VCF pieces in parallel (16 per batch today), proven to give
the same output as the sequential machine.

The proposal adds an option `--threads N`, so a user can size the work to their hardware: the
batch size, the driver's read-ahead and reference reads in flight, and Bend's worker threads.
The design and the drafted diff are in `notes/threads.md` (sections "The option" to "The drafted
diff"); nothing tracked is edited yet. In short:
- `B.Args.parse` (`types.bend`) accepts `--threads N`, N from 1 to 128, anywhere among the
  options, the last one counting; `Opts` and `Cfg` do not change, and the header's recorded
  command line (`Opts.args`) leaves out `--threads` and its value. A new `B.Args.threads` reads N.
- A new `law threads` in `MACHINE.bend`: `--threads N` right after `norm` gives the same `launch`
  (paths, stdout bytes, messages, exit code) as the same command line without it.
- The runtime's thread count follows N through a C constructor in the trusted driver that sets
  `BENDRTS` (the runtime's own option) before `main`.

Review the law change, not the code (the code and proofs come after this review, and the driver
part gets its own driver review). Questions:
1. Does `law threads`, with `law machine` and `law usage`, say what a user needs: that N can
   never change the output? Is there any command line where N changes something the laws do not
   cover, or where the law could hold while the program misbehaves (for example a statement that
   is true for a reason that has nothing to do with threads)?
2. The parser changes: is the new grammar unambiguous and the same as before for every command
   line without `--threads` (byte-for-byte the same `Cfg`, including `Opts.args`)? Check the
   drafted examples, including `--threads` as the value of `-f` and a missing value.
3. Answer the author's five questions at the end of `notes/threads.md` with your own view:
   leaving `--threads` out of the recorded header line; the range (1 to 128, 0, no limit);
   "right after norm" against any position; the parser fact as a lemma or a law; the C
   constructor against documenting `+RTS --threads N -RTS`.
4. Anything a scientist reviewing these laws would find unclear, or a simpler statement.

Use only the repository's files (`notes/threads.md`, `types.bend`, `MACHINE.bend`, `LAWS.bend`,
`examples.bend`, `docs/LAWS.md`, `notes/briefs/THREADS.md`); you do not need anything under
`data/`. You may run `bend` checks only on copies under `/tmp`.

Report a numbered list: severity (blocker / should fix / minor), the exact place, why, and the
fix. Or say ACCEPT. Be brief. End with the full report as your final message.
