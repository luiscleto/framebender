Not ACCEPT. Four findings.

1. **Should fix.** `io64_wall` in `io64.c:779` calls `write` while `SIGXFSZ` is still the default, which kills the process. `test/out.sh:172` hides this with `trap '' XFSZ`.
   Input: `prlimit --fsize=80 /tmp/fb-d8/fb norm -c w -f test/edge/ref.fa -Oz -o /tmp/sig.vcf.gz test/edge/sorted.vcf`
   The shell status is 153, `File size limit exceeded`. Stderr stops in the notes and never prints `error: cannot write`. The same run with the signal ignored exits 2, prints `error: cannot write /tmp/sig.vcf.gz`, and leaves no end-of-file block.
   Fix: `signal(SIGXFSZ, SIG_IGN)` once before any output `write`, so `write` returns `EFBIG` and `io64_wall` reports it. Drop the trap in `test/out.sh`.

2. **Should fix.** `io_out_close_run` in `io64.c:1130` writes the 28-byte end-of-file block, then `io64.c:1135` checks `close`. On Linux a failed `close` still releases the descriptor, so the block cannot be taken back. A BGZF file is then complete while the process exits 2.
   Input: an `LD_PRELOAD` that makes `close` of the `-o` descriptor return `EIO`, then `/tmp/fb-d8/fb norm -c w -f test/edge/ref.fa -Oz -o /tmp/fb-d8/closefail.vcf.gz test/edge/sorted.vcf`
   Exit 2, stderr ends with `error: cannot write /tmp/fb-d8/closefail.vcf.gz`, and the file is 525 bytes, byte-identical to `bgzip -l 6` of the plain output, end-of-file block included.
   Fix: remember the size before the end-of-file block. If `close` fails and the file is regular, open that path again and `ftruncate` back to the saved size, then return the close error. A pipe cannot be unsent.

3. **Should fix.** `io64_out_open` in `io64.c:1038` compares device and inode only when `S_ISREG`. The same FIFO as the VCF and as `-o` is not refused, and the write end stays open, so the next read never sees end-of-file.
   Input:
   ```
   mkfifo /tmp/fb-d8/onefifo
   cat test/edge/sorted.vcf > /tmp/fb-d8/onefifo &
   /tmp/fb-d8/fb norm -c w -f test/edge/ref.fa -o /tmp/fb-d8/onefifo /tmp/fb-d8/onefifo
   ```
   The process does not exit. The main thread stays in `anon_pipe_read`; notes are already on stderr and there is no `output is an input`. `timeout 3` exits 124. The same shape with `-o /dev/stderr` and stderr itself a FIFO exits 0 and writes the VCF text to that FIFO (981 bytes). A separate FIFO as `-o` is fine and matched `bgzip`.
   Fix: compare the VCF, the FASTA, and the `.fai` for every file type. Compare stderr for regular files and FIFOs, and skip character devices so `-o /dev/stdout` on a terminal still works. On a match, `close` the new descriptor and return 2001. Call `ftruncate` only for a regular file.

4. **Minor.** `test/out.sh:249`. A failed run still exits 0, because the last command is `echo`.
   Input: `bad=1; [ $bad = 0 ] && echo "OUT OK" || echo "OUT FAILED"` prints `OUT FAILED` and returns status 0.
   Fix: `exit "$bad"`.

Byte identity with `bgzip -l L` held for levels 0–9 on `test/edge/sorted.vcf`, and for the generated cut files (header longer than a block, header ending on a block boundary, incompressible data) at `--threads 1` and `128`. No block exceeded 65536 bytes. A machine exit 1 keeps a prefix and writes no end-of-file block. Missing inputs leave an existing `-o` file unchanged. Regular-file identity refuses the VCF, a symlink, a hard link, the FASTA, the `.fai`, `/proc/self/fd/N`, `/dev/stdin`, and stderr redirected onto that file, before truncating. A directory, `/dev/full`, `/dev/null`, and `/dev/stdout` behave as the comment says. A finished run with no output bytes (`error: NO_HEADER`) leaves the `-o` file empty, which is that run's output.
