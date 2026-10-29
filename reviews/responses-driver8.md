# Responses to driver review 8 (compressed output, phase H, 2026-10-29)

Prompt: `DRIVER8_PROMPT.md`. Reports: `claude-driver8.md`, `gpt-driver8.md` (GPT 6.1 Sol),
`grok-driver8.md` (Grok 4.7). None accepts yet; every finding is in the trusted output path, none
in the laws. Claude checked the ring, the compressors, the writer, the carried tail, CRC32/ISIZE,
the level map, the memory bound and the constructor's grammar and found them correct; Grok
confirmed byte identity with `bgzip -l L` at levels 0-9 and on the generated cut files at
`--threads 1` and 128, and the refusals of regular-file inputs by every name.

## Decisions (for the compress agent)

1. **Refuse a pipe or FIFO that is an input** (Claude, Grok; both reproduced a hang:
   `cat in.vcf | fb ... -o /dev/stdin /dev/stdin`, and one FIFO given as both VCF and `-o`).
   Compare (dev, ino) with the VCF, the FASTA and the `.fai` for every file type; with stderr for
   regular files and FIFOs (skip character devices, so `-o /dev/stdout` on a terminal works). On
   a match close the new descriptor and refuse ("output is an input"). `ftruncate` only regular
   files.
2. **Ignore `SIGXFSZ`** (GPT, Grok; both reproduced death by signal, status 153, under
   `prlimit --fsize`): `signal(SIGXFSZ, SIG_IGN)` before the first output write, so `write` returns
   `EFBIG` and the run reports "cannot write" (exit 2) with no end-of-file block. Drop the
   `trap '' XFSZ` from `test/out.sh` so the test sees the real behaviour.
3. **A failed `close` after the end-of-file block** (GPT, Grok; both reproduced a complete-looking
   file with exit 2 by injecting `EIO` into `close`). Remember the size before the end-of-file
   block; if `close` fails on a regular file, open the path again and `ftruncate` it back to that
   size, then report the error. A pipe cannot take bytes back: law machine's comment says so in
   one clause.
4. **`test/out.sh` exits with its result** (GPT, Grok): `exit "$bad"`.
5. **The final carried bytes as bgzip writes them** (Claude, minor): when the last full window
   ended exactly at the end of the text, queue the carried bytes as one block, as bgzip's trailing
   `bgzf_write` does, so the comment's claim (bgzip's bytes for any text) holds even for a text
   without a final LF. If that is not simple, narrow the comment to texts ending in LF (the
   machine always ends its text with one).
6. **Comment** (Claude): after a driver error the BGZF file decompresses to a prefix of the output
   bytes (the carried bytes are not written): "a prefix of them (all of them when the machine
   finished)".
7. **Tests** (Claude): a transient write failure (stdout a non-blocking pipe whose reader pauses,
   one `EAGAIN`) with the output checked as a prefix of bgzip's bytes; identity by `/dev/stdin`,
   `/proc/self/fd/0` and a FIFO input; a failing assertion in out.sh section 6 (the constructor's
   `-o`/`-O` grammar: the threads seen); "no BGZF in this build" for output on a one-step build;
   the close failure (decision 3) and the file-size limit (decision 2).

Then the three reviewers check the fixes (round 2).

## Who caught what (Q4)

- Pipe/FIFO identity: Claude and Grok. Grok also showed `-o /dev/stderr` with stderr a FIFO.
- `SIGXFSZ`: GPT and Grok, both noticing the test's `trap` hid it.
- EOF block then failed `close`: GPT and Grok (both with an injected `EIO`).
- `test/out.sh` exit status: GPT and Grok.
- The final carried bytes, the prefix comment, the missing tests: Claude only.

## Round 2 (`*-driver8-r2.md`)

Grok: ACCEPT. Claude: ACCEPT with four minor items (its round-1 file `claude-driver8.md` is its
plan draft; the final round-1 items are restated in `claude-driver8-r2.md`). GPT: two should-fix
items, both in the take-back after a failed `close`. Decisions:

8. **The take-back checks identity and is best effort** (GPT 1, Claude 2; GPT reproduced a
   truncated FASTA through a path re-pointed to it): keep the output's (dev, ino) from the first
   open; reopen, `fstat`, and `ftruncate` only on a match. When the take-back cannot be done (the
   path changed, or cannot be reopened, as with umask 0777), the error is still reported (exit 2)
   and the file may keep its end-of-file block: law machine's comment says the take-back is best
   effort (GPT 2), and a test covers a failed take-back.
9. **Compare with stderr only when stderr is a regular file** (Claude 1): output and messages
   sharing a pipe or terminal is what the user asked for (`-o /dev/stdout 2>&1 | tail`), loses no
   data and cannot hang; emptying a regular file would wipe the messages. The `-o /dev/stderr`
   FIFO test becomes an accepted case.
10. **Tests** (Claude 3, 4): an `LD_PRELOAD` `write()` shim that fails the k-th output write once
    with `EIO` and lets later ones through, then the file must be a prefix of bgzip's bytes with no
    end-of-file block; `gen_out.py` says `tailwin` cannot tell the `wend` fix apart (the machine
    always ends with LF), plus a direct C test of the cut on a text without a final LF if simple.

Amended after the fixes: the author proposed keeping a duplicate of the output descriptor (`dup`)
until the close, and truncating through it after a failed `close`. No path lookup, so nothing to
re-point, and it works under umask 0777: the take-back is then exact for regular files, not best
effort. Adopted in place of the reopen.

Who caught what: the path re-pointed (GPT, Claude); the failed take-back under umask 0777 (GPT);
the stderr pipe refusal, the weak EAGAIN test, the unreachable `tailwin` (Claude).

## Round 3 (`*-driver8-r3.md`)

Grok accepted in round 2; Claude accepts. GPT, both with a second injected failure: (1) a failed
`close` of the duplicate is ignored (exit 0); (2) a failed `ftruncate` through the duplicate leaves
the end-of-file block with exit 2. Decisions:

11. Check the duplicate's `close` and report a failure ("cannot write <path>", exit 2).
12. The take-back is exact unless it fails itself: if the `ftruncate` through the duplicate fails,
    or the duplicate's own `close` fails after it, the error is reported (exit 2) and the file may
    keep its end-of-file block. Law machine's comment and `docs/LAWS.md` say so in one clause; a
    test injects a failed `ftruncate`.

The lead checks these two with GPT's reproduction (`/tmp/fb-review8-r3/finalization.py`) instead
of a fourth round: they only report errors and narrow a sentence.
