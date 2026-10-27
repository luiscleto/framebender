Review of the trusted driver (read-only: do not modify, create or delete files).

The two-layer spec is now in place on the current branch (root files `LAWS.bend`, `types.bend`,
`run.bend`, `tan.bend`, `protocol.bend`, `MACHINE.bend`) and every law is proven (`./check.sh`:
bend and `--verdict`). The one part no law covers is the driver, `main.bend`: it is trusted code.
The comment on law `machine` in `MACHINE.bend` lists exactly what the driver must do (read the
files' bytes; answer each read of an `Ask` with `truth(...)`, in order, through the `.fai` index;
write the stdout bytes and `B.Note.render` of each message; exit with the code; the usage and
unreadable-file errors). The migration added the code that answers a list of reads
(`answers`, `answers.k`, `answers.cons`); the rest is as before.

Check `main.bend` against that comment: is there any way the driver does something other than what
the comment says (wrong order of answers, a read clipped differently from `truth`, a byte changed
on the way in or out, a message lost, a wrong exit code, an unhandled error)? Report a numbered list
(severity, the exact place, a concrete input that triggers it, the fix), or say it is correct.
Be brief; final answer.
