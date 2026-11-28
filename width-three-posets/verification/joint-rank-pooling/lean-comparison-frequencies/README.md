# Lean-checked joint rank pooling for finite-poset rankings

For the existing finite-poset Ranking and exclusive-branch definitions,
the new Lean theorem
WidthThree.jointComparisonCount_of_branchRankSum proves

    count(a<x) + count(a<y) ≤ 2 (count(a<u) + count(a<v))

whenever all four vertices lie in the branch, the predecessor condition
holds, and every ranking R satisfies

    rank_R(x) + rank_R(y) ≤ 2 (rank_R(u) + rank_R(v)).

The Rank here is the one-based position in the induced branch order.
The companion theorem
WidthThree.jointComparisonFrequency_of_branchRankSum proves the same
exact inequality for the rational normalized values F. These equal
uniform comparison probabilities when the ranking population is
nonempty.

The proof turns the conditional BinGiven counts into finite antitone
lists using the checked recurrence and swap inequality, invokes the
exact cutoff-mixture arithmetic, and sums the local inequalities over
a four-position partition of all rankings. No conditional XYZ
inequality is used.

## Scope and replay

Pinned Lean 4.36.0 and Mathlib
fc4f59e577feb1a4956671bc04ac18aaaf8cd842 checked both endpoint
declarations and a separate import-and-type audit. The endpoints
depend only on propext, Classical.choice, and Quot.sound. The generic
conditional-list connector depends only on propext and Quot.sound.
The filenames and top comments still say Draft to preserve the
exact compiled source bytes.

This result does not transfer the geometric rank estimates for the
ladder or crossed-tail families, and does not prove the width-three
conjecture. The written structural arguments remain separate.

With the compiled prerequisite modules and Mathlib on LEAN_PATH,
run ./replay.sh. For a source-only rebuild, set REBUILD_PREREQS=1
and put Mathlib on LEAN_PATH. The bundled prerequisite files are
BranchSwap, BranchOrder, MultiRankStep, JointCapDraft and
AntitonePrefixDraft; the new files are compiled serially in
ConditionalBinListDraft, JointBranchOrderDraft, JointBranchOrderAudit
order. The interpreter memory cap defaults to 2500 MB and only one
Lean worker is used. Verify staged files with sha256sum -c SHA256SUMS.
