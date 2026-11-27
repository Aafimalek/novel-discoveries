import NineSeparatedSubsetSums.Profile158

namespace NineSeparatedSubsetSums

set_option maxRecDepth 8192

/-- Rank labels are zero-based in this file. In every cube ordering with edge
length at most 148, positions 158 and 306 (one-based) are neighbors. -/
theorem forced_rank_edge (r : Cube 9 ≃ Fin 512)
    (hspan : ∀ x y : Cube 9, near 9 x y → (r x).val ≤ (r y).val + 148) :
    near 9 (r.symm 305) (r.symm 157) := by
  classical
  let P := (Finset.Iio (158 : Fin 512)).map r.symm.toEmbedding
  have hp : P.card = 158 := by simp [P]
  have memP (x : Cube 9) : x ∈ P ↔ (r x).val < 158 := by
    constructor
    · intro hx
      obtain ⟨j, hj, hjx⟩ := Finset.mem_map.mp hx
      change r.symm j = x at hjx
      subst x
      have hj' := Finset.mem_Iio.mp hj
      change j.val < (158 : Fin 512).val at hj'
      simpa only [Equiv.apply_symm_apply] using hj'
    · intro hx
      exact Finset.mem_map.mpr ⟨r x, Finset.mem_Iio.mpr hx, r.symm_apply_apply x⟩
  let B := (closed 9 P).image (fun x => (r x).val)
  have hi : Function.Injective (fun x => (r x).val) :=
    fun _ _ h => r.injective (Fin.ext h)
  have hb : 306 ≤ B.card := by
    change 306 ≤ ((closed 9 P).image (fun x => (r x).val)).card
    rw [Finset.card_image_of_injective _ hi]
    exact cube9_closed_of_card158 P hp
  have hs : B ⊆ Finset.range 306 := by
    intro j hj
    change j ∈ (closed 9 P).image (fun x => (r x).val) at hj
    obtain ⟨x, hx, he⟩ := Finset.mem_image.mp hj
    obtain ⟨y, hy, hxy⟩ := mem_closed.mp hx
    have h₁ := (memP y).mp hy
    have h₂ := hspan x y hxy
    exact Finset.mem_range.mpr (by omega)
  have hB : B = Finset.range 306 :=
    Finset.eq_of_subset_of_card_le hs (by simpa using hb)
  have h305 : 305 ∈ B := by
    rw [hB]
    exact Finset.mem_range.mpr (by omega)
  change 305 ∈ (closed 9 P).image (fun x => (r x).val) at h305
  obtain ⟨x, hx, hrx⟩ := Finset.mem_image.mp h305
  obtain ⟨y, hy, hxy⟩ := mem_closed.mp hx
  have hp' := (memP y).mp hy
  have hz := hspan x y hxy
  have hry : (r y).val = 157 := by omega
  have ex : x = r.symm 305 := by
    apply r.injective
    rw [r.apply_symm_apply]
    exact Fin.ext hrx
  have ey : y = r.symm 157 := by
    apply r.injective
    rw [r.apply_symm_apply]
    exact Fin.ext hry
  rwa [ex, ey] at hxy

#print axioms forced_rank_edge

end NineSeparatedSubsetSums
