# C14 exact archive through 604 learned clauses
The checked theorem is
    Euler.C14.Production.exactArchiveThrough9429ViaPolarity :
      GoodBelow archivedGlobalCore rowAt 9429.
This verifies the exact sorted archive plus 604 contiguous learned
clauses, not the terminal empty clause or 36-officers geometry.

The prior formally checked 599-prefix follows the exact same rowAt
construction and contains the previously hard 510-hint polarity row.
Its forty pinned source/object/log records were revalidated before the
single serialized build. The only changes to the staged runner in this
isolated replay directory were role-specific receipt path resolution
(frozen456 vs current overlay), pinning the exact prior checkpoint
JSON, and adding the frozen456 object roots to LEAN_PATH. All four
staged Lean files are byte-identical to the original staged sources.
The prior and staging directories were not modified.

Strict pinned Lean 4.36, -j1, -M2450, warnings-as-errors, overlay TMPDIR
and the shared single-worker lock; duration 29.86 s wall / 26.16 user /
2.78 sys, caps unchanged 160s global, 47s per leaf. The three checked
production slices cover 5 new exact clauses, 606 hint references, ending
at raw ID11647. Each leaf and conditional aggregate uses only propext;
the unconditional archive-prefix theorem uses only propext,
Classical.choice, Quot.sound. No retries or native evaluation.

Guaranteed replay dependency: exact through9424 source SHA
855e0c1c3234bae904b20c36059ee060aa14b36cdbe0274f79f0c5ae05e9d4f5
and audit SHA 4891b1c79eb299bfb9b082f8364ae9ecc6365b075e1a8e5b4b1d57f2c853b268.
See independent local object receipts and ordinary strict logs.
