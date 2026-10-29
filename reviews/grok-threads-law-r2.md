# Grok law review: --threads, round 2

ACCEPT.

Round 1 is closed. `law threads` now inserts `--threads N` at every `pre` with `Args.expecting(pre)`, so the usual line and a flag after the VCF path are inside the statement. One `N` equals the line without it, so two values of `N` agree, and a repeated flag comes off one pair at a time. `Args.threads` is `Some` only on a line `Args.parse` accepts: `Args.thr.done` uses the same success pattern as `Args.done` (`PNone`, both paths, `ok`), and the first word must be `norm`. An out-of-range value clears `ok` for good, so a returned `n` is between 1 and 128. The `008`, path, `0`, `999`, bad command word, trailing `--threads`, and missing-`-f` examples match that.

`Args.expecting` is exactly the state in which a further option is still legal: after `Args.init()`, `pend` is `PNone` and `ok` is still true (right after `norm`, after a finished value, after the VCF path). It is false while a value is pending (`-f`, `-c`, `-w`, `--threads`) and after an error. After an error the parser will still take the token `--threads`, and both lines are usage errors, so the output claim stays closed there.
