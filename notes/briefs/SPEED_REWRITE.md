# Brief: records that are rewritten (fb-rewrite)

Read `notes/briefs/SPEED_COMMON.md` first. On `data/scr.vcf` (HG002's 20,739 indels moved to
random positions, so almost every record is left-aligned and rewritten) framebender takes
0.12-0.13 s against bcftools' 0.07-0.08 s (README's results). It is the one plain input where
bcftools is faster. Records that need rewriting go through `norm_fix.bend` on bytes, or to the
String path (`norm_seq.slow`) when it refuses them; `notes/bytes.md` and `notes/fast.md` have the
older profiles (60% in reference counting of shared Strings inside the String judge and
`Rec.rebuild`, when scr still took the slow path for almost every record).

**Your part:**
1. Profile scr at `--threads 1` and the default (gprof build, or `perf`), find where the time goes
   now (which records still take the String path and why, the window and reference reads, the
   rewrite itself, the sorting buffer when records move), and make it faster in the proven part,
   proven equal to what it replaces.
2. If it is on the way: `norm_fix.bend` still refuses any INFO with an END entry (`NF.noend`), so a
   rewritten record with END takes the String path. fb-end added the END scan for the fast path
   (`ends` in `norm_fast.bend`, `proof_b_end_key.bend`); `notes/briefs/END.md` fix 1's second
   half is reusing it in `norm_fix.bend` with `Info.set_end` on bytes. Do it if it fits; say if
   not.

This branch has fb-tasks, fb-refuse and fb-end merged. fb-memory is changing `-m`'s record
output at the same time (`norm_split.bend`, the split dispatch in `norm_seq.bend`, `norm.bend`'s
output reserve): keep out of those, and keep changes to `norm_seq.bend` small and local.

**Measure** scr and a second scramble (`test/scramble.py`, another seed; `data/tmp/rewrite/`), the
END file and gVCF shapes from `data/tmp/fb-end/` with indels scrambled, before and after, with
bcftools beside them; HG002 chr22 and whole genome (default and `--threads 1`), which must not get
slower.
