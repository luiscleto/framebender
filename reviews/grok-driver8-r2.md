ACCEPT. Each finding is fixed, and the fixes hold on the re-runs.

A pipe or FIFO named by `-o` is refused and the new descriptor is closed, so the run exits 2 instead of hanging. Checked: one FIFO as both the VCF and `-o`, `cat in.vcf | fb -o /dev/stdin /dev/stdin`, `-o /proc/self/fd/0`, and `-o /dev/stderr` with stderr a FIFO (the error line only, 38 bytes). A separate FIFO still matches `bgzip -l 6`. `-o /dev/stdout` with stdout and stderr the same terminal still writes the VCF. Regular-file identity is unchanged: the VCF, a symlink, a hard link, the `.fai`, and `/proc/self/fd/N` are refused with the file left as it was. A missing VCF leaves an existing `-o` file unchanged.

`SIGXFSZ` is ignored from the output's open on. `prlimit --fsize` with no shell trap exits 2 with `error: cannot write <path>`, the file a prefix of the successful output and no end-of-file block (limits 80, 50, 1000, and 10 and 28 bytes short of a whole BGZF file). The same holds for stdout redirected to a regular file.

A `close` that returns `EIO` after the end-of-file block exits 2, and the file is `bgzip -l 6` of the plain output minus those 28 bytes (497 against 525).

`test/out.sh` ends with `exit "$bad"`. A copy of that ending with `bad=1` prints `OUT FAILED` and exits 1.

The carried tail matches bgzip. `tailwin` (output exactly 65280 bytes) and a header that ends on the first block boundary match `bgzip -l 6` at `--threads 1` and `128`. So do the other generated files, including `rand` at level 0 (8 blocks, largest 65311). A machine exit 1 (`test/edge/in.vcf`, `-c e`) is that text in BGZF with no end-of-file block.

Law machine's comment now says a failed close of a regular `-o` file cuts the end-of-file block back off, a pipe cannot, and a BGZF file decompresses to a prefix of the output bytes, all of them when the machine finished.

The new transient-failure case, on a non-blocking pipe of 65536 bytes with `-Oz0`, exits 2 with `error: cannot write`, 61741 bytes, a prefix of bgzip's bytes and no end-of-file block. The process had already exited before the pipe was drained.
