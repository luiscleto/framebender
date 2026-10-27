You are reviewing a change to framebender's implementation contract. framebender is a VCF normalizer
in Bend 2. Its science layer (`LAWS.bend`, `types.bend`, `run.bend`, `tan.bend`: what the tool
must output) is unchanged. The implementation contract says that the program (a state machine
driven by a trusted driver) writes exactly what the science layer defines. It is two files:
- `protocol.bend`: the types between program and driver;
- `MACHINE.bend`: the law `machine` and its driver definition.

The change moves the program's input and output from Strings (linked lists of characters, slow) to
packed byte buffers (`lawful-bytes`, which you reviewed). Proving the new program is a later step.

Read in `../framebender`, on the git branch `bytes` (read-only: do not modify anything, do not
switch branches):
- `git diff main -- protocol.bend MACHINE.bend`: the change.
- `bytes_enc.bend` (new): `text` (a buffer's bytes as characters, one Char per byte) and `enc` (the
  canonical buffer for a text: bytes four to a word, little-endian, zero-padded, in the smallest
  block that holds them).
- The full `protocol.bend` and `MACHINE.bend`, especially the trust-boundary comment above
  `law machine`.
- `test/enc_spot.bend` checks `text(enc(s)) == s` on a few texts.

The design:
- The law's statement is unchanged: for every way the VCF is cut into String pieces `cs`, the
  program's report equals `run`.
- The driver definition now feeds each piece as `E.enc(c)` and answers each reference read with
  `E.enc` of the letters. It reads the program's output buffer as `E.text(o)`.
- The trusted driver must build exactly `E.enc` (the canonical packing) for pieces and answers. It
  must write exactly the bytes of `D.view(o)`. It refuses reads of 2 GiB or more.

Answer:
(a) Does the changed law still say what it said before: the program's output, messages and exit
    code are exactly `run`'s, for all inputs? Could a program satisfy the new law and still
    write wrong bytes, given a driver that does what the comment says?
(b) Is the canonical `enc` well defined, and is requiring the driver to build exactly it (padding
    and block size included) reasonable for a C implementation? Would a weaker requirement (any
    buffer whose text is the piece) be better, and how would the law state it?
(c) `text` maps byte b to `Chr{b}`, and the driver reads files one Char per byte. Is anything lost
    between the file's bytes and the spec's Strings (bytes >= 128, NUL, CR)?
(d) The 2 GiB limit per piece and per reference read: is it stated where it must be? Can the
    driver always keep to it (it chooses the piece size; answers are windows of a contig, and
    chr1 is about 250 MB)?
(e) Anything else in the diff that is wrong or weaker than before.

Report a numbered list of findings. For each: where; severity (blocker / should fix / minor); the
problem; an example; a fix. End with the full report as your final message. If nothing is wrong,
say ACCEPT.
