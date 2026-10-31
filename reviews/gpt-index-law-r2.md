1. **Should fix — truncation before sidecar removal**, [notes/index.md:1163](/home/luisc/Work/bend-projects/framebender-index/notes/index.md:1163), [prototype `idx_unlink_old`](/home/luisc/Work/bend-projects/framebender-index/data/tmp/index/proto/io64.c:1113). Decision 2’s order leaves stale indexes when removal fails, contradicting decision 14’s guarantee. Confirmed with an injected `EPERM`: exit 2, output reduced from 247 bytes to zero, both old indexes retained. A directory permission check cannot guarantee removal. **Fix:** stage both sidecars before truncation, restoring them if truncation fails; abort before truncation if staging fails. Test failure on each sidecar.

2. **Should fix — format-independent differential oracle**, [notes/index.md:1290](/home/luisc/Work/bend-projects/framebender-index/notes/index.md:1290). “If either refuses” wrongly requires CSI failure whenever TBI refuses. Confirmed at POS 600,000,000: prototype CSI succeeds and equals `bcftools index`; tabix refuses TBI. **Fix:** compare CSI with `bcftools index` and TBI with `tabix -p vcf` separately. Handle unsuccessful normalization first: preserve its report/output and require no new index.

The other decisions are reflected in the revised design and prototype. `index_sink` is true as stated and satisfies decision 5; deriving `Args.index` from `Args.sink` supplies the required connection. No approved law is weakened, and previously accepted commands retain their `Cfg`.

Answers to the round-2 questions:

1. Accept the lock on the superset of lines containing `END=`.
2. Fix the ordering as above; permission prechecks are insufficient.
3. Use a separate prefix such as `~/.local/opt/htslib-1.24-nocurl`, selected through `PKG_CONFIG_PATH`; retain the drafted refusal of a curl-enabled build.
4. Accept the temporary names with `O_EXCL` and bounded retries.
5. Keep the second usage line, as decision 15 requests.
6. Keep removal without `-W` as a separate contract change.
7. Prioritize profiling INFO/END separately before recommending gVCF workloads.

Repository unchanged; executable checks used copies under `/tmp`.
