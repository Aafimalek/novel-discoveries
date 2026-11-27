import EulerAllUsedPinProfile

namespace LatinGap.PairEncoding

/-- One numeric witness covers the exact shared support+counter blocks,
the two original anchor pins, and the 28-clause all-used profile block.
The six low-low pair bits follow as a separate semantic consequence. -/
structure AllUsedPinCommon (D : Design 6) (W : Coord → Word 6) (v : ℕ → Bool) : Prop where
  core : ∀ x : Var 6, v (varNumber x) = (encode D).eval x
  degrees : ∀ (g : Coord) (a : Fin 6) (d : Fin 7),
    v (degreeThresholdNumber g a d) = decide (d.val ≤ freq D (g,a))
  support : ∀ c ∈ archivedSupportPrefix, NumberedHolds v c
  count : ∀ c ∈ archiveProjectionCountBlock, NumberedHolds v c
  excess : ∀ g : Coord, ∀ c ∈ archiveDegreeExcessCountBlock g, NumberedHolds v c
  anchors : ∀ c ∈ archiveAllUsedAnchorUnits, NumberedHolds v c
  pins : ∀ c ∈ archiveAllUsedPinProfile (actualRowCodes W), NumberedHolds v c
  lowPairs : ∀ c ∈ allUsedZeroPairUnits, NumberedHolds v c

theorem actual_allUsed_pin_common {D : Design 6} (lin : Linear D) (sat : Saturated D)
    (size : D.card = 17) (zero : (fun _ => 0) ∈ D)
    (profile : ∀ (g : Coord) (a : Fin 6), freq D (g,a) = if a=0 then 2 else 3)
    (W : Coord → Word 6) (hw : ∀ i, W i ∈ D)
    (pub : actualRowCodes W ∈ EulerAllUsedDiagrams.published) :
    ∃ v : ℕ → Bool, AllUsedPinCommon D W v := by
  let base := designNumeric D
  have hm (g : Coord) (a : Fin 6) : 2 ≤ freq D (g,a) := by
    rw [profile]; by_cases hz : a=0 <;> simp [hz]
  have wr (w : Word 6) : base (wordNumber w) = (encode D).select w := designNumeric_core D (.word w)
  have pr (p : PairKey 6) : base (pairNumber p) = (encode D).pair p := designNumeric_core D (.pair p)
  obtain ⟨v,keep,supp,count,excess⟩ := geometry_satisfies_archived_prefix_and_cardinality
    D lin sat size hm base wr pr (designNumeric_degree D)
  have cr (x : Var 6) : v (varNumber x) = (encode D).eval x :=
    (keep _ (Or.inl (varNumber_le_1512 x))).trans (designNumeric_core D x)
  have vd (g : Coord) (a : Fin 6) (d : Fin 7) :
      v (degreeThresholdNumber g a d) = decide (d.val ≤ freq D (g,a)) :=
    (keep _ (.inr (degreeThresholdNumber_bounds g a d))).trans (designNumeric_degree D g a d)
  exact ⟨v,cr,vd,supp,count,excess,
    allUsed_archive_anchors_holds D v (fun w => cr (.word w)) zero W hw pub,
    allUsed_archive_pin_profile_holds D v (fun w => cr (.word w)) vd W hw profile,
    allUsed_zero_pair_holds D v (fun p => cr (.pair p)) zero⟩

#print axioms actual_allUsed_pin_common
end LatinGap.PairEncoding
