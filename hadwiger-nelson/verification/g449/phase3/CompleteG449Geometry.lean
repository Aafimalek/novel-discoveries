import OrbitCheck
import AllRoots
import Rotation42
import AllPublishedEdges

namespace PlaneColouring.Cyclotomic42

open G449OrbitArithmetic

/-- Coefficient interpretation of the independently parsed model. -/
def orbitDir (d : ℕ) : Coeff := fun i => dirs d i.val
def orbitPowers (k : Fin 54) : Coeff := fun i => powers k.val i.val

theorem spin_bridge (v : G449OrbitArithmetic.V) (i : Fin 12) :
    spin v i.val = rotateSix (fun j => v j.val) i := by
  fin_cases i <;> rfl

theorem powers_bridge : checkedPowers orbitPowers := by
  have h := checkedPowersArithmetic
  unfold testPowers at h
  simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at h
  refine ⟨?_,?_⟩
  · intro i
    rw [show orbitPowers 0 i = powers 0 i.val from rfl, h.1 _ (List.mem_range.mpr i.isLt)]
    fin_cases i <;> rfl
  · intro k i
    change powers (k.val+1) i.val = shift (orbitPowers k.castSucc) i
    rw [h.2 _ (List.mem_range.mpr k.isLt) _ (List.mem_range.mpr i.isLt)]
    fin_cases i <;> rfl

theorem bare_norm_bridge (k : ℕ) (i : Fin 12) :
    normBare powers (dirs k) i.val = normCoeffs orbitPowers (orbitDir k) i := by
  simp only [normBare, List.sum_ofFn, normCoeffs, orbitPowers, orbitDir, indexPow]

theorem representative_norm (k : ℕ) (hk : roots.contains k = true) :
    normUnreduced (orbitDir k) = (49^2 : ℂ) := by
  have hmem : k ∈ roots := List.contains_iff_mem.mp hk
  have ht := (List.all_eq_true.mp roots_checked_math) k hmem
  have H (i : Fin 12) : normCoeffs orbitPowers (orbitDir k) i = (49^2 : ℤ) * start i := by
    rw [← bare_norm_bridge, testNorm_sound _ _ ht i.val i.isLt]
    fin_cases i <;> decide
  have hn := eval_normCoeffs orbitPowers powers_bridge (orbitDir k)
  rw [show normCoeffs orbitPowers (orbitDir k) = fun i => (49^2 : ℤ)*start i from funext H] at hn
  have he : eval (fun i => (49^2 : ℤ)*start i) = (49^2 : ℂ) := by
    unfold eval
    simp only [Int.cast_mul, Int.cast_pow, Int.cast_ofNat,mul_assoc,← Finset.mul_sum]
    change 49^2 * eval start = (49^2 : ℂ)
    rw [eval_start,mul_one]
  rw [he] at hn
  rw [normUnreduced_eq, ← hn]

/-- All 49 exact signed direction classes used by the input edge list
have unit squared distance after division by the original denominator. -/
theorem all_49_direction_norms (k : ℕ) (hk : k < 49) :
    normUnreduced (orbitDir k) = (49^2 : ℂ) := by
  suffices K : ∀ r, ∀ j : ℕ, j < 49 → (parent j).rank = r →
      normUnreduced (orbitDir j) = (49^2 : ℂ) by
    exact K _ k hk rfl
  intro r
  induction r using Nat.strongRecOn with
  | ind r ih =>
    intro j hj hr
    have chk := (List.all_eq_true.mp all_steps_arithmetic) j (List.mem_range.mpr hj)
    rcases orbitStepBool_sound dirs parent roots j chk with base | ⟨hp,hd,heq⟩
    · exact representative_norm j base
    have nb := ih (parent (parent j).prev).rank (hd.trans_eq hr) _ hp rfl
    cases hf : (parent j).spinNeg with
    | false =>
      have e : orbitDir j = rotateSix (orbitDir (parent j).prev) := by
        funext t
        change dirs j t.val = rotateSix (fun i => dirs (parent j).prev i.val) t
        simpa only [hf, Bool.false_eq_true, ↓reduceIte, spin_bridge] using heq t.val t.isLt
      rw [e, norm_rotateSix, nb]
    | true =>
      have e : orbitDir j = fun t => -rotateSix (orbitDir (parent j).prev) t := by
        funext t
        change dirs j t.val = -rotateSix (fun i => dirs (parent j).prev i.val) t
        simpa only [hf, ↓reduceIte, spin_bridge] using heq t.val t.isLt
      rw [e, normUnreduced_neg, norm_rotateSix, nb]

theorem all_49_direction_displacements_unit (k : Fin 49) :
    dist (point (orbitDir k.val)) (point (fun _ => 0)) = 1 := by
  apply dist_one_of_unreduced
  rw [show diff (orbitDir k.val) (fun _ => 0) = orbitDir k.val from funext (fun i => sub_zero _)]
  exact all_49_direction_norms k.val k.isLt

#print axioms powers_bridge
#print axioms all_49_direction_norms
#print axioms all_49_direction_displacements_unit


def vertexCoeffs (k : ℕ) : Coeff := fun i =>
  (vertices k).coeffs.getD i.val 0

/-- The point from the published integer coordinate row, with denominator 49. -/
noncomputable def sourcePoint (k : ℕ) : Plane := point (vertexCoeffs k)

theorem source_colour_palette (k : ℕ) (hk : k < 449) : (vertices k).colour < 5 :=
  decide_eq_true_eq.mp (List.all_eq_true.mp palette_five k (List.mem_range.mpr hk))

/-- All edges of the published list are actual unit-distance edges, and
the values from the published five-colour assignment differ on them. -/
theorem published_edge_unit_and_proper (e : Edge) (he : e ∈ allPublishedEdges) :
    e.a < 449 ∧ e.b < 449 ∧
      dist (sourcePoint e.a) (sourcePoint e.b) = 1 ∧
      (vertices e.a).colour ≠ (vertices e.b).colour := by
  have hbool := List.all_eq_true.mp all_edge_links e he
  obtain ⟨ha,hb,hd,hc,h⟩ := Edge.validBool_sound vertices dirs e hbool
  refine ⟨ha,hb,?_,hc⟩
  unfold sourcePoint
  apply dist_one_of_unreduced
  cases hf : e.flip with
  | false =>
    have hdir : diff (vertexCoeffs e.a) (vertexCoeffs e.b) = orbitDir e.d := by
      funext i
      simpa only [diff, vertexCoeffs, orbitDir, hf, Bool.false_eq_true, ↓reduceIte] using h i.val i.isLt
    rw [hdir, all_49_direction_norms _ hd]
  | true =>
    have hdir : diff (vertexCoeffs e.a) (vertexCoeffs e.b) = fun i => -orbitDir e.d i := by
      funext i
      simpa only [diff, vertexCoeffs, orbitDir, hf, ↓reduceIte] using h i.val i.isLt
    rw [hdir, normUnreduced_neg, all_49_direction_norms _ hd]

theorem geometry_and_five_colouring :
    allPublishedEdges.length = 2198 ∧
      (∀ k < 449, (vertices k).colour < 5) ∧
      ∀ e ∈ allPublishedEdges, dist (sourcePoint e.a) (sourcePoint e.b) = 1 ∧
        (vertices e.a).colour ≠ (vertices e.b).colour := by
  refine ⟨number_of_edges, source_colour_palette, ?_⟩
  intro e he
  exact (published_edge_unit_and_proper e he).2.2

#print axioms source_colour_palette
#print axioms published_edge_unit_and_proper
#print axioms geometry_and_five_colouring

end PlaneColouring.Cyclotomic42
