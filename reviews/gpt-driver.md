# GPT, driver review
• The batching helpers preserve answer order. I found two concerns elsewhere in
  the driver: reference offsets are narrowed to 32 bits, and command-line
  arguments are decoded as Unicode before being written through a byte-only
  path. I’m checking the runtime’s read and error handling to confirm the
  consequences.

• Exited (status 2) rg -n 'File\.|stdout|stderr|stdin|fd|io_str\(|io_cbuf|io_cs…
  └ /home/luisc/.bend/bend2/base.bend:337:def File.write(file: File, data: Stri…
    /home/luisc/.bend/bend2/base.bend:342:def File.write_bytes(file: File, data…
    /home/luisc/.bend/bend2/base.bend:347:def File.close(file: File) -> IO(Unit…
    + 14 lines (^t to expand)

• Explored
  └ List bend2
    Search (io|runtime|\.h$)
    Read ref.fa
    + Show details

• Ran python3 -B - <<'PY' …
  └ pipe stdout: 1 stdout bytes: 273 stderr: error: REF_MISMATCH    t1    5    …
    socket stdout: 2 stdout bytes: 0 stderr: error: cannot read /dev/stdout
    + 1 line (^t to expand)

• Ran python3 -B - <<'PY' …
  └ VCF directory: 2 b'' b'error: cannot read the VCF file\n\n'
    FASTA base offset 4294967296 becomes U32 0
    FASTA base offset 4294967300 becomes U32 4
    + Show details

• Explored
  └ Search Term io_str|io_str\(|static .*io_cbuf|io_cbuf\( in .bend
    List .bend
    Search Halt|stderr|newline|IO.die in EFFECTS.md
    + Show details

• Ran python3 -B - <<'PY' …
  └ args: [] exit: 2 stdout: b'' stderr: b'usage: framebender norm -f ref.fa [-…
    args: ['norm', '-f', '/definitely-missing-framebender-ref.fa', 'test/edge/i…
    + 2 lines (^t to expand)

• The batching helpers preserve answer order. I found these driver issues:

  1. Blocker — reference offsets wrap at 4 GiB, main.bend:189 (main.bend:189).
     U32.from_nat(o0) truncates the file offset. A contig starting at byte
     4294967296 is read from byte zero, producing false reference answers. Fix:
     use 64-bit file offsets without narrowing.

  2. Should fix — incomplete reference reads become “truthful” answers,
     main.bend:168 (main.bend:168). The runtime performs one pread, capped at
     INT32_MAX bytes; the driver neither retries nor checks completeness. A
     request spanning more than that returns a truncated Known. Fix: read in
     bounded pieces until the requested bases are collected; detect unexpected
     EOF.

  3. Should fix — Unicode arguments violate byte preservation, main.bend:302
     (main.bend:302), with str_bytes at line 40. IO.args decodes Unicode, but
     str_bytes treats each code point as one byte. A readable α.fa causes header
     writing to fail because α exceeds 255; é.fa writes byte E9 instead of UTF-8
     C3 A9. Fix: use IO.args_bytes, preserve arguments as bytes, and open paths
     with File.open_bytes.

  4. Should fix — reopening stdout/stderr rejects valid inherited streams,
     main.bend:282 (main.bend:282). With stdout connected to a socket pair, the
     existing executable exits 2 with cannot read /dev/stdout, despite stdout
     being writable. Fix: use the inherited descriptors directly instead of
     reopening /dev/stdout and /dev/stderr.

  5. Minor — usage and driver errors gain an extra newline, main.bend:105
     (main.bend:105) and main.bend:289 (main.bend:289). Confirmed: invoking
     without arguments prints B.usage followed by another LF; this runtime’s
     IO.die adds a newline. Fix: write the exact diagnostic bytes, then exit 2.

  6. Minor — read failures omit the required path, main.bend:256
     (main.bend:256), likewise lines 121 and 167. Using . as the VCF path prints
     cannot read the VCF file rather than cannot read .. Fix: retain each path
     and use it in read-error diagnostics.

