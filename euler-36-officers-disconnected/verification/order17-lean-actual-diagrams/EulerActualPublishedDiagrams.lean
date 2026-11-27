import EulerActualOuterTable
import EulerAllUsedDiagramShards

namespace LatinGap
open EulerAllUsedDiagrams

/-- The actual geometry's valid canonical data lies in the published
seventeen-diagram table, using the separate kernel-checked shards. -/
theorem outerColumns_canonical_published (U : Coord → Word 6)
    (hz : ∀ i, U i i = 0) (hpat : ∀ j, outerColumn U j ∈ outerPatterns)
    (h : ∀ i j u v : Coord, i ≠ j → u ≠ v → U i u = U j u → U i v ≠ U j v) :
    canonical (ofColumns (outerColumns U)) ∈ published :=
  validInput_is_published _ _ _ _ (hpat 0) (hpat 1) (hpat 2) (hpat 3)
    (outerColumns_oneOverlap U hz h)

private theorem foldl_smallest_origin (a : List Nat) (xs : List (List Nat)) :
    let out := xs.foldl (fun p q => if compare p q == .gt then q else p) a
    out = a ∨ out ∈ xs := by
  induction xs generalizing a with
  | nil => simp
  | cons x rest ih =>
    simp only [List.foldl_cons]
    split
    · rcases ih x with h | h
      · exact Or.inr (List.mem_cons.mpr (Or.inl h))
      · exact Or.inr (List.mem_cons_of_mem x h)
    · rcases ih a with h | h
      · exact Or.inl h
      · exact Or.inr (List.mem_cons_of_mem x h)

/-- If the canonical answer is an archived diagram, it is realized by
normalizing an actual coordinate permutation in the finite table. -/
theorem canonical_origin_of_published (m : List (List Nat))
    (hp : canonical m ∈ published) :
    ∃ p ∈ allPermutations, normalize m p = canonical m := by
  rcases foldl_smallest_origin [9999] (allPermutations.map (normalize m)) with e | e
  · change canonical m = [9999] at e
    rw [e] at hp
    exact ((by decide : [9999] ∉ published) hp).elim
  · change canonical m ∈ allPermutations.map (normalize m) at e
    exact List.mem_map.mp e

/-- Integrates the actual geometry with the checked 17-output audit.
The chosen list of coordinate indices still needs to be implemented as
a physical permutation of the design and its individual symbols. -/
theorem all_used_actual_published {D : Design 6} (hD : Linear D)
    (hS : Saturated D) (a : Word 6) (ha : a ∈ D)
    (hfreq : ∀ j, freq D (j,a j) = 2) :
    ∃ E : Design 6, Linear E ∧ Saturated E ∧ E.card = D.card ∧
      (fun _ => 0) ∈ E ∧ (∀ j, freq E (j,0) = 2) ∧
      ∃ U : Coord → Word 6, Function.Injective U ∧
        (∀ i, U i ∈ E ∧ U i i = 0 ∧ ∀ j ≠ i, U i j ≠ 0) ∧
        ∃ p ∈ allPermutations,
          normalize (ofColumns (outerColumns U)) p = canonical (ofColumns (outerColumns U)) ∧
          normalize (ofColumns (outerColumns U)) p ∈ published := by
  obtain ⟨E,hE,hm,sz,hz,hf,U,ui,uw,hpat,one⟩ :=
    normalize_all_used_outer_patterns hD hS a ha hfreq
  have hp := outerColumns_canonical_published U (fun i => (uw i).2.1) hpat one
  obtain ⟨p,hpperm,hpnormal⟩ :=
    canonical_origin_of_published (ofColumns (outerColumns U)) hp
  exact ⟨E,hE,hm,sz,hz,hf,U,ui,uw,p,hpperm,hpnormal,hpnormal ▸ hp⟩

#print axioms outerColumns_canonical_published
#print axioms canonical_origin_of_published
#print axioms all_used_actual_published
end LatinGap
