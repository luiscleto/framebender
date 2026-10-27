# Driver review (bytes branch): responses (2026-10-27)

Reviewers: Claude (Opus 5.5), GPT (GPT-6.1-Sol), Grok (4.7). No blocker. All three built and ran
the driver; GPT's direct effect tests covered:
- 68 canonical packing cases;
- 90 reference windows with padding checks;
- offsets above 4 GiB;
- a span crossing the 16 MiB read boundary;
- short and interrupted I/O;
- closed and full stdout.

Claude ran the whole genome: 7 s, 0 differing records against bcftools, FASTA offsets above 2^31.
No wrong byte was found anywhere.

| finding | raised by | severity | change |
|---|---|---|---|
| `.fai` read (Base `File.read_bytes`) treats EINTR as fatal | GPT | should fix | read the index with a retrying effect |
| `.fai` line length, line width and column passed as U32: a line of 2^32 bytes or more wraps and is refused ("unsupported FASTA"; fails closed, never a wrong slice) | Claude, Grok | minor | pass them as 64-bit halves, like the offset |
| `Io.write_block` trusts that its argument is a packed buffer | Claude | minor | check the tag and class; EINVAL otherwise |
| Out of memory reported as "cannot read" (and one leak on that path) | Claude | minor | a distinct "out of memory" error, listed in the trust comment |
| Blocks of n <= 4 bytes leave 4 bytes of their 8-byte cell uninitialized (never read) | Claude | minor | zero the whole cell |
| Little-endian assumed | Claude | minor | `#error` on big-endian |
| A path containing LF makes a two-line error | GPT | minor | escape LF (and CR) in paths in driver errors |
