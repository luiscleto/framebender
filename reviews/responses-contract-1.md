# Contract review round 1: responses (2026-10-27)

| finding | raised by | change |
|---|---|---|
| The law quantifies over every String, but buffers hold bytes: a header with Chr{256} makes it false for every program | Claude, GPT, Grok (blocker) | hypothesis `hb: E.texts_ok(argv, fasta, cs)`: all characters below 256 (`E.is_bytes`) |
| Pieces over 2^31 bytes do not fit a buffer (and 2^32 wraps `U32.from_nat`) | Claude, GPT, Grok | `E.texts_ok` also requires each piece to have at most 2^31 bytes (`E.pieces_ok`) |
| Output buffers need not be well formed; a C driver writing len bytes could read past the block | Claude | `absorb` reads output through `E.out`: the text of a perfect block of depth <= 29 holding len bytes, else the run's `good` flag clears and `result` is None |
| The reference-read size limit is only in the driver | Claude, GPT | `dstep` clears `good` if any read asks for more than 2^31 letters (`E.reqs_ok`); the driver must answer every smaller window, reading a larger physical span (line breaks) in parts |
| `main.bend` header still says 4 GiB | Grok | passed to the bytes agent, who owns the driver on this branch |
| The contract does not type-check; `Norm.Step`'s output type lives in program code | Claude, GPT | expected until the program is ported (phase A); the law fixes the output's shape (`Norm.Step{st, o, ns, nx}` with `E.out(o)`) |

Not taken: a weaker requirement than the exact `E.enc` packing for inputs (GPT): it needs a driver
relation quantified over all well-formed buffers with the right text, and representation-
independence proofs; the exact packing is easy for C to build.

## Rounds 2 and 3

- Round 2: Claude and Grok accepted. GPT (blocker): the step bound ignored the command line, which
  `run` echoes into the header, while one step now writes at most 2^31 bytes; a 146 GB argument made
  the law unsatisfiable. `bound` now adds `args_len(argv)`, and `launch` takes `argv`. Claude: the
  trust comment now says `P.Ask{[]}` gets another step (for output beyond 2^31 bytes).
- Round 3: Claude, GPT and Grok accepted (2026-10-27, 10:16-10:18 PM).
