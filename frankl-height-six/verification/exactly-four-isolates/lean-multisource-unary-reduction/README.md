# Two verified multi-source reductions (not full exclusion)

Both modules compiled cleanly on pinned Lean 4.36.0 and Mathlib,
importing the rebuilt ambient dependency closure. All eight theorem
audits use only propext, Classical.choice and Quot.sound. The audit
records exact stdout and two zero exit statuses in replay.log.

- FranklFourSupportUnary: weak families with no empty member
  contain no member of size below three; at most five original
  members fit inside a support of four points. Applying this to
  the checked multileaf anchor gives
  exact_four_proper_forcing_successor_unique: with four isolates
  and at least two sources, each source has a unique proper
  forcing successor. No general 12-point theorem is assumed.
- FranklMultipleSourceTraceObstruction: the full isolate trace
  has at least as many physical preimages in a source-containing
  fiber as there are sources. In particular isolate projection
  on that fiber is not injective with two or more sources. This
  delimits, rather than generalizes, the verified one-source
  trace classifier.

For a portable replay, extract the included archive. Verify
`sha256sum -c sources.sha256` and run
`MATHLIB_ROOT=/path/to/pinned/mathlib4 LEAN_BIN=/path/to/lean bash rebuild.sh`.
It includes the 18 freshly rebuilt ambient-source dependencies and
these two checked modules. The written `no-small-ground-refinement.md`
gives a conditional roadmap through the earlier
[at-least-five-isolates argument](https://github.com/Aafimalek/novel-discoveries/tree/99abc567470ea8669712272bee26b25a81a0b6ee/frankl-height-six/verification/at-least-five-isolates).
The atom counts, link partitions and mixed witnesses for the full
multi-source contradiction have not been verified end to end in Lean.
