Review of framebender's trusted driver on the git branch `bytes` (read-only: do not modify, create
or delete files, and do not switch branches).

framebender's program is now proven against packed byte buffers (or will be: the proofs are the
next phase). The contract, which you reviewed and accepted, is in `MACHINE.bend` and
`bytes_enc.bend`. The comment above `law machine` lists exactly what the driver must do:
- read the files' bytes, one character per byte;
- hand each VCF piece to the program as exactly `E.enc` of its text: bytes four to a word,
  little-endian, zero-padded, in the smallest perfect block that holds them, with pieces of at
  most 2^31 bytes;
- answer each reference read `Req{chrom, a, b}` of an `Ask`, in order, with exactly
  `truth(B.Fasta.parse(fasta), chrom, a, b)`, packed by `E.enc`. It reads through the `.fai` index
  at 64-bit offsets, reading any physical span in parts, and never refuses a window of at most 2^31
  letters;
- answer `P.Ask{[]}` as an ordinary step;
- write exactly the bytes of each output buffer (`D.view(o)`: its first len bytes) and every
  message (`B.Note.render`), then exit with the code;
- report its own errors, each as one line on stderr with exit code 2.

The driver is `main.bend` (Bend: the loop, `.fai` parsing, answering reads) and `io64.c` (C
effects: reading a file range into a packed block, writing a block's bytes, raw fd writes).
`io64.js` holds stubs. `git diff main -- main.bend io64.c` shows the change from the reviewed
String driver. `notes/bytes.md`, section "The trusted driver", describes it.

Check the driver against that comment. Is there any way it does something other than what the
comment says? Look for, among others:
- a block that is not exactly `E.enc`: wrong depth, padding, length or word order, or a last
  partial word;
- an answer clipped or offset differently from `truth`;
- reads at offsets of 4 GiB or more;
- partial reads or writes, and EINTR;
- a byte changed on the way in or out (CR, bytes >= 128, NUL);
- writing past the end of a block, or memory errors in the C code (bounds, `malloc` failure,
  integer overflow in sizes);
- a message lost, or a wrong exit code;
- `P.Ask{[]}` not handled.

You may build and run it on small inputs (`bend main.bend -o /tmp/fb_review`, then
`/tmp/fb_review norm -f test/edge/ref.fa test/edge/sorted.vcf`), and you may write test files under
`/tmp` only.

Report a numbered list: severity (blocker / should fix / minor), the exact place, a concrete
input that triggers it, and the fix. Or say ACCEPT. Be brief. End with the full report as your
final message.
