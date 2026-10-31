# Brief: END= lines on bytes (fb-end)

Read `notes/briefs/SPEED_COMMON.md` first. The investigation is `notes/briefs/END.md`: every record
with an INFO/END entry leaves the bytes fast path (`noend` in `norm_fast.bend`, its copy in
`norm_fix.bend`) and is decoded into a String, about 13x slower on chr22 with END on every record;
gVCF's symbolic ALTs take the same slow path.

**Your part:** fixes 1 and 2 of `END.md` ("Proposed fix, cheapest first"): check a valid END on
bytes (and set it on bytes for records that are rewritten), then judge BAD_END and Skipped
(out of scope, e.g. `<NON_REF>`) on bytes. Fix 3 (tasks keeping their notes) belongs to fb-tasks;
don't touch the merge (`norm.bend`'s `merge.ok`, `proof_e_merge_*`).

**Measure** on `data/tmp/end/`'s generators (`gen_end.py`, `gen_gvcf.py`; the large test files
were deleted, regenerate them under `data/tmp/fb-end/`), chr22 with valid END, with 2% bad END,
and the gVCF shapes, before and after; and the HG002 chr22 and whole genome without END, which
must not get slower.
