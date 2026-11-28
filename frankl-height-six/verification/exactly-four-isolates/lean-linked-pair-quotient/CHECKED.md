# Checked linked pair quotient

The four new source files were replayed with pinned ordinary Lean 4.36,
one worker, 2,500 MB Lean memory limit, overlay temporary storage, and
warnings treated as errors. All ten axiom audits gave exactly
`[propext, Classical.choice, Quot.sound]`. See the replay log.

Endpoint `FranklForcingFiber.exact_four_disjointTriple_anchors_full_isolate_omissions`
concerns an actual four-isolate pair fiber with two explicit disjoint
triple blocks through its anchors. The anchors each have degree k−2,
their own block is an ordinary pair, and the caller supplies the
pair-design identities `N+2t=choose(k,2)` and `3t≤k`. Then all
isolates are present in the raw pair maximum, and deleting any one
isolate from it yields another member of the original pair-avoiding
family. The theorem does not assert all deficit-one families have these
hypotheses or exclude deficit one or two.

The source-only `portable/` bundle contains the recursively gathered
61-module closure in dependency order with pinned revision, source
manifest and standalone rebuild script. The current receipt is from
compilation of the four new modules against already checked imports,
not a fresh rebuild of that complete portable closure.
