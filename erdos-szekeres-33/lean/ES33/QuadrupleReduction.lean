import Mathlib.Basic.Real.Basic
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.Convex.Independent
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.Dimension.Constructions

namespace ES33

abbrev Plane := ℝ × ℝ

/-- Convex position means each selected point is a vertex of the convex hull.
This is not the empty-polygon property. -/
def ConvexPosition (s : Finset Plane) : Prop :=
  ConvexIndependent ℝ (Subtype.val : ↥(s : Set Plane) → Plane)

/-- A planar nonvertex has a certificate consisting of at most three other points. -/
theorem small_nonvertex_witness {s : Finset Plane} {x : Plane}
    (hx : x ∈ convexHull ℝ ((s : Set Plane) \ {x})) :
    ∃ t : Finset Plane, (t : Set Plane) ⊆ (s : Set Plane) \ {x} ∧
      t.card ≤ 3 ∧ x ∈ convexHull ℝ (t : Set Plane) := by
  rw [convexHull_eq_union] at hx
  simp only [Set.mem_iUnion, exists_prop] at hx
  obtain ⟨t, hsub, hAffine, hx⟩ := hx
  have hb := hAffine.card_le_finrank_succ
  have hd : Module.finrank ℝ Plane = 2 := by
    simp [Plane, Module.finrank_prod]
  have hle := Submodule.finrank_le (vectorSpan ℝ (Set.range (Subtype.val : ↥t → Plane)))
  rw [hd] at hle
  have hb : Fintype.card ↥t ≤ 3 := hb.trans (Nat.add_le_add_right hle 1)
  simpa only [Fintype.card_coe] using
    (show ∃ u : Finset Plane, (u : Set Plane) ⊆ (s : Set Plane) \ {x} ∧
        Fintype.card ↑u ≤ 3 ∧ x ∈ convexHull ℝ (u : Set Plane) from ⟨t,hsub,hb,hx⟩)

/-- For any set of at least four points, testing all four-subsets
is necessary and sufficient for convex position. No general-position
assumption is needed for this geometric reduction itself. -/
theorem convexPosition_iff_quadruples {s : Finset Plane} (hs : 4 ≤ s.card) :
    ConvexPosition s ↔ ∀ q : Finset Plane, q ⊆ s → q.card = 4 → ConvexPosition q := by
  classical
  constructor
  · intro h q hq _
    exact ConvexIndependent.mono (𝕜 := ℝ) h (Finset.coe_subset.mpr hq)
  · intro h
    rw [ConvexPosition, convexIndependent_set_iff_notMem_convexHull_sdiff]
    intro x hxs hx
    obtain ⟨t, ht, hcard, hxt⟩ := small_nonvertex_witness (s := s) hx
    have hinc : insert x t ⊆ s := by
      intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact hxs
      · exact (ht hy).1
    have hfour : (insert x t).card ≤ 4 := by
      have hle := Finset.card_insert_le x t
      omega
    obtain ⟨q, hiq, hqs, hqcard⟩ := Finset.exists_subsuperset_card_eq hinc hfour hs
    have hq := h q hqs hqcard
    rw [ConvexPosition, convexIndependent_set_iff_notMem_convexHull_sdiff] at hq
    refine hq x (hiq (Finset.mem_insert_self x t)) ?_
    apply convexHull_mono (𝕜 := ℝ) ?_ hxt
    intro y hy
    exact ⟨hiq (Finset.mem_insert_of_mem hy), (ht hy).2⟩

/-- Exact combinatorial quantifier pattern needed by an ES(7) SAT encoding. -/
theorem no_heptagon_iff_every_seven_has_bad_four (s : Finset Plane) :
    (¬ ∃ t : Finset Plane, t ⊆ s ∧ t.card = 7 ∧ ConvexPosition t) ↔
      ∀ t : Finset Plane, t ⊆ s → t.card = 7 →
        ∃ q : Finset Plane, q ⊆ t ∧ q.card = 4 ∧ ¬ ConvexPosition q := by
  classical
  constructor
  · intro h t ht hcard
    have h7 : 4 ≤ t.card := by omega
    by_contra nh
    apply h
    refine ⟨t, ht, hcard, (convexPosition_iff_quadruples h7).2 ?_⟩
    intro q hq hqcard
    by_contra notq
    exact nh ⟨q,hq,hqcard,notq⟩
  · rintro h ⟨t,ht,hcard,hconv⟩
    obtain ⟨q,hq,hqcard,notq⟩ := h t ht hcard
    exact notq (ConvexIndependent.mono (𝕜 := ℝ) hconv (Finset.coe_subset.mpr hq))

#print axioms small_nonvertex_witness
#print axioms convexPosition_iff_quadruples
#print axioms no_heptagon_iff_every_seven_has_bad_four

end ES33
