1. **Should fix — [io64.c:1176](/home/luisc/Work/bend-projects/framebender-gz/io64.c:1176).** The duplicate descriptor’s `close()` error is ignored. Injecting `EIO` only on the second output close produces exit 0 and no error, for both plain and BGZF output. **Fix:** check this close and report its failure; document the EOF exception if final-close failure prevents rollback.

2. **Should fix — [io64.c:1171](/home/luisc/Work/bend-projects/framebender-gz/io64.c:1171), [MACHINE.bend:189](/home/luisc/Work/bend-projects/framebender-gz/MACHINE.bend:189).** A duplicate makes recovery independent of the pathname and permissions, but `ftruncate()` can still fail. Injecting `EIO` into the first close and rollback truncate leaves the complete EOF marker with exit 2. **Fix:** retain descriptor-based recovery, describe rollback as best effort, and test failed truncation.

Both reproduce on the fresh build with [finalization.py](/tmp/fb-review8-r3/finalization.py).

Both round-2 reproductions now pass: the FASTA stays unchanged and EOF removal works under `umask 0777`. All 480 byte comparisons and the targeted write-error, size-limit, descriptor-limit, and pipe checks passed. Repository unchanged.
