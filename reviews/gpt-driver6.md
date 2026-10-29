# Driver review 6 (`--threads N`): GPT 6.1 Sol

I’ll compare the driver changes with the `law machine` contract, then check the runtime argument split, batching, and I/O ordering. I’ll keep the repository unchanged and use only `/tmp` for any build or test artifacts.
The batching and reference-read changes preserve the existing order, and the new ring depth is set once before the first file read. I’ll now check the constructor against the Bend parser and generated C runtime, including argument splitting and the user’s `BENDRTS` settings.
The constructor matches the generated runtime’s `+RTS`/`-RTS`/`--RTS` split and preserves the user’s later `BENDRTS` settings. I haven’t found a defect so far. Next I’ll run targeted comparisons at N = 1 and 128, using small-piece builds to exercise ring wraparound and batch boundaries.
All 84 edge-case comparisons passed byte for byte across the tested thread counts and both piece sizes. On truncated BGZF input, changing the piece size can change how much stdout appears before the read error; both builds still report the required one-line error and exit 2. I’ll compare successful inputs byte for byte and check driver failures separately.
The constructor matched `B.Args.threads` in 447 targeted and randomized cases. The sanitizer checks also passed for those cases, existing `BENDRTS` values, and the 1 MiB command-line limit. Both build paths succeeded. I’m finishing with larger synthetic inputs for ring wraparound and ordered reference-error checks.
ACCEPT.
