import EulerGeometryValuation
import EulerArchivedCounterValuation
import EulerAnchorNormalize

namespace LatinGap.PairEncoding

/-- The common normalized degree-two input blocks covered so far. This is
not the whole archived formula: support-AMO auxiliary states and the
later symmetry and branch-specific constraints are deliberately absent. -/
structure MinTwoCommon (D : Design 6) (v : ℕ → Bool) : Prop where
  coreRead : ∀ x : Var 6, v (varNumber x) = (encode D).eval x
  degreeRead : ∀ (g : Coord) (a : Fin 6) (d : Fin 7),
    v (degreeThresholdNumber g a d) = decide (d.val ≤ freq D (g,a))
  symbolicCore : SatisfiesClauses (liftNumbers v) 17
  degreeBlocks : ∀ (g : Coord) (a : Fin 6) (C : List Int),
    C ∈ degreeBlock 2 g a → NumberedHolds v C
  projection : ∀ C ∈ archiveProjectionCountBlock, NumberedHolds v C
  excess : ∀ g : Coord, ∀ C ∈ archiveDegreeExcessCountBlock g, NumberedHolds v C

/-- One numbered valuation satisfies the blocks covered by MinTwoCommon,
all at once, for any actual normalized degree-two hypothetical design. -/
theorem minTwoCommon_of_design {D : Design 6} (hD : Linear D) (hM : Saturated D)
    (size : D.card = 17) (hmin : ∀ x : Label 6, 2 ≤ freq D x)
    (h0 : freq D (0,0) = 2) : ∃ v : ℕ → Bool, MinTwoCommon D v := by
  let base := designNumeric D
  have hpc (p : PairKey 6) : base (pairNumber p) = (encode D).pair p :=
    designNumeric_core D (.pair p)
  obtain ⟨v,keep,hpr,hex⟩ := geometry_satisfies_archived_cardinality D hD size
    (fun g a => hmin (g,a)) base hpc (designNumeric_degree D)
  have hcore (x : Var 6) : v (varNumber x) = (encode D).eval x :=
    (keep _ (Or.inl ((varNumber_le_1512 x).trans (by decide)))).trans (designNumeric_core D x)
  have hdegree (g : Coord) (a : Fin 6) (d : Fin 7) :
      v (degreeThresholdNumber g a d) = decide (d.val ≤ freq D (g,a)) :=
    (keep _ (Or.inr (degreeThresholdNumber_bounds g a d))).trans (designNumeric_degree D g a d)
  refine ⟨v, hcore,hdegree,?_,?_,hpr,hex⟩
  · have same (x : Var 6) : v (varNumber x) = base (varNumber x) :=
      keep _ (Or.inl ((varNumber_le_1512 x).trans (by decide)))
    have he : liftNumbers v = liftNumbers base := by
      have hW : (liftNumbers v).select = (liftNumbers base).select := funext fun w => same (.word w)
      have hP : (liftNumbers v).pair = (liftNumbers base).pair := funext fun p => same (.pair p)
      cases hv : liftNumbers v
      cases hb : liftNumbers base
      simp only [hv,hb] at hW hP
      congr
    rw [he,designNumeric_lifts]
    exact (satisfiesClauses_iff _ _).2 (encode_satisfies hD hM size)
  · intro g a C hc
    have hf : (fun b => v (pairNumber (degreeNeighborPair g a b))) =
        (fun b => (encode D).pair (degreeNeighborPair g a b)) :=
      funext fun b => hcore (.pair (degreeNeighborPair g a b))
    apply degreeBlock_holds v 2 g a (freq D (g,a)) ?_ (hdegree g a) ?_ C hc
    · rw [hf, patternCount_eq_freq hD g a]
    · refine ⟨hmin (g,a),?_⟩
      rintro ⟨rfl,rfl⟩
      exact h0

/-- A hypothetical size-17 design of minimum two can be renamed to the
two archived anchor words and satisfies all currently covered blocks. -/
theorem minTwoCommon_of_min_degree_two {D : Design 6}
    (hD : Linear D) (hM : Saturated D) (size : D.card = 17)
    (x : Label 6) (hmin : ∀ y : Label 6, 2 ≤ freq D y) (hx : freq D x = 2) :
    ∃ E : Design 6, (fun _ => 0) ∈ E ∧ (fun i => if i=0 then 0 else 1) ∈ E ∧
      ∃ v : ℕ → Bool, MinTwoCommon E v := by
  obtain ⟨E,hE,hME,hc,hm,h0,ha,hb⟩ := normalize_degree_two_anchor hD hM x hmin hx
  exact ⟨E,ha,hb,minTwoCommon_of_design hE hME (hc.trans size) hm h0⟩

#print axioms minTwoCommon_of_design
#print axioms minTwoCommon_of_min_degree_two
end LatinGap.PairEncoding
