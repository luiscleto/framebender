# Brief: warn about an old index left by a run without -W (fb-staleidx)

framebender is a VCF normalizer in Bend 2 whose behaviour is fixed by laws and proven
(`docs/LAWS.md`). The trusted driver (`main.bend`, `io64.c`, `build.sh`) does the effects the
laws leave out; MACHINE.bend's comment on law `machine` ("What this law does not cover") states
what it promises. Phase J (`-W`, `notes/index.md`, `reviews/*driver9*`) writes an index and moves
old ones aside.

**The problem.** `framebender norm -o out.vcf.gz ...` without `-W` rewrites `out.vcf.gz` and
leaves an old `out.vcf.gz.csi`, `out.vcf.gz.tbi` (or the stem `out.vcf.csi`, which htslib also
tries; see the phase J notes on htslib 1.24's search order) as it was. Region queries
(`bcftools view -r`, `tabix`) then read the stale index; htslib warns only when the index is a
second or more older than the file. `docs/USAGE.md` ("Old index files") documents it today.

**The change.** When `-o` names a BGZF file and `-W` is not given, and any index name htslib
would try for that file exists, print one warning per such file to stderr, e.g.
`warning: out.vcf.gz.csi is an index of the old out.vcf.gz; remove it or use -W`. Do not remove
or touch it (it may index another file, as `out.vcf.csi` may index `out.vcf`). Choose when to
check (before anything is read is simplest, so it shows even if the run stops later), and say
why. Nothing else changes: output bytes, exit codes, the other messages, `-W` runs, stdout and
plain `-o` runs.

**Scope.** Driver only: `main.bend`, `io64.c` and their comments, `MACHINE.bend`'s comment on
what the driver does (no law, no definition the proofs use), `docs/USAGE.md` (the "Old index
files" part and the differences list if it applies), and tests in `test/index.sh` (each index
name, CSI and TBI, a directory or symlink at an index name, a run that stops, a plain `.vcf` and
stdout with an index next to them: no warning). `check.sh` must still pass in both modes.

**How to work.** Branch `stale-index` from main; `BEND_NO_TELEMETRY=1`; proof checks only through
`test/bcheck.sh` (two at a time machine-wide, others are proving); scratch in
`data/tmp/staleidx/`; `rm` only with literal paths. Commit on your branch; don't push or merge.
No timing is needed beyond a check that a run without an index next to it is not slower (the
lock `flock data/tmp/bench.lock` if you time anything).

**Report** (final message): the message and when it is printed, the files changed, the tests
and their results, check.sh in both modes, the commits.
