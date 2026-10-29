1. **Should fix — [io64.c:1161](/home/luisc/Work/bend-projects/framebender-gz/io64.c:1161).** Close-error recovery reopens the pathname without checking its identity. Reproduced by injecting close `EIO` and replacing that path with a symlink to the FASTA: recovery resized the input from 55 to 512 bytes. **Fix:** retain the original output’s device/inode and verify the reopened descriptor before truncating, or recover through a retained descriptor.

2. **Should fix — [io64.c:1160](/home/luisc/Work/bend-projects/framebender-gz/io64.c:1160).** EOF removal remains fallible, despite the unconditional guarantee. With `umask 0777`, a newly created output is writable through its original descriptor, but recovery cannot reopen it. Injected close `EIO` therefore still leaves the complete EOF marker with exit 2. **Fix:** explicitly document recovery as best effort, including regular files, or redesign finalization to meet the guarantee. Test failed recovery too.

Both cases reproduce with [close_repro.py](/tmp/fb-review8-r2/close_repro.py).

All other listed fixes passed. Rechecked the original reproductions, 480 byte comparisons, and 72 direct tail-boundary cases. Repository unchanged.
