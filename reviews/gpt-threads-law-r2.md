# GPT law review: --threads, round 2

ACCEPT.

The round-1 findings are resolved. `Args.expecting(pre)` captures valid option boundaries: no prior error and no pending value, including after the VCF path. Repeated thread options can therefore be removed individually.

`Args.threads` now checks `norm` and the same completed-state conditions as `Args.parse`; `Some{n}` consequently implies acceptance and 1 ≤ n ≤ 128.

Together with `machine` and `usage`, the revised law has no new hole identified.
