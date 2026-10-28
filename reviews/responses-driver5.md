# Driver review 5 (branch `driver2`): responses

Reviewers: Claude (`claude-driver5.md`), GPT 6.1 Sol (`gpt-driver5.md`), Grok 4.7
(`grok-driver5.md`). Prompt: `DRIVER5_PROMPT.md`. All three: ACCEPT. Claude: three minor notes,
none asking for a change.

| # | finding | by | verified | response |
|---|---|---|---|---|
| 1 | An out-of-memory stop can now come before an earlier read's error: a group's later reads take their blocks before the first read's error is reported. Only with an Ask whose first read is bad and whose later reads are near 2^31 letters each | Claude | from the code (`main.bend` `starts`, `io64.c` `fa_start`); not run (it needs tens of GB) | No change. The runtime's out-of-memory stop (exit 1) is already listed in `MACHINE.bend`; a successful Ask's peak is unchanged, since the old driver also held all of an Ask's answers. |
| 2 | A full ticket table (a 33rd read before a wait) would surface as `cannot read`, not as a broken invariant | Claude | from the code; all three reviewers found no path that starts a 33rd read | No change: unreachable. Recorded in case the batch size changes. |
| 3 | The heap-full fallbacks (the ring reading the piece itself, ENOMEM at a wait) never run on CPU builds, where a full heap stops the runtime first | Claude | yes (`err_seen` is false on CPU; same as review 4, finding 2) | No change: the header comment of `io64.c` already says so. |

Evidence beyond the code: GPT ran 49 checks (queue wraparound, FASTA lines across the 1 MiB
buffer, BGZF damage, competing errors in one Ask and across groups, both build paths). Grok ran
competing errors at piece size 1000 and pipe and FIFO early stops. Claude ran 264 comparisons
per piece size on damaged inputs, 96 on a 61 MB input that fills the ring, ThreadSanitizer,
AddressSanitizer and UBSan (no reports touching the driver), and failure injection for thread
creation and buffer allocation. Every comparison was identical to the previous driver.

Q4 note: no reviewer found a defect. The three cover each other's blind spots this time: GPT and
Grok wrote tests from the open questions, Claude added the sanitizers and fault injection that
the earlier reviews lacked.
