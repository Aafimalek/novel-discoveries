import NineSeparatedSubsetSums.FinsetDirection
import NineSeparatedSubsetSums.ProjectionCount
import NineSeparatedSubsetSums.ProjectionLift
import NineSeparatedSubsetSums.FinsetSlab
import Mathlib.Tactic.NormNum

namespace NineSeparatedSubsetSums

/-- A 149-element interval of width M projects to at least 148 subsets.
The sole possible repeated projection is the lower endpoint, since
first-coordinate base scores are injective. -/
theorem critical_projection_large {ι : Type*} [DecidableEq ι]
    (U : Finset ι) (w : ι → ℝ) (c M : ℝ) (F : Finset (Finset ι × Bool))
    (hbase : Set.InjOn (slabScore w) {S : Finset ι | S ⊆ U})
    (hm : ∀ (S : Finset ι) (b : Bool), (S, b) ∈ F ↔
      S ⊆ U ∧ c ≤ liftScore M (slabScore w S) b ∧ liftScore M (slabScore w S) b ≤ c + M)
    (hcard : F.card = 149) :
    148 ≤ (F.image Prod.fst).card := by
  classical
  have eq (S : Finset ι) (hs : (S, false) ∈ F) (ht : (S, true) ∈ F) :
      S ⊆ U ∧ slabScore w S = c := by
    have ha := (hm S false).mp hs
    have hb := (hm S true).mp ht
    exact ⟨ha.1, two_lifts_only_at_endpoint c M (slabScore w S) ha.2.1 hb.2.2⟩
  have ex : ∃ S0 : Finset ι, ∀ S, (S, false) ∈ F → (S, true) ∈ F → S = S0 := by
    by_cases h : ∃ S : Finset ι, (S, false) ∈ F ∧ (S, true) ∈ F
    · obtain ⟨S0, h1, h2⟩ := h
      refine ⟨S0, ?_⟩
      intro S h3 h4
      have a := eq S h3 h4
      have b := eq S0 h1 h2
      exact hbase a.1 b.1 (a.2.trans b.2.symm)
    · exact ⟨∅, fun S h1 h2 => (h ⟨S, h1, h2⟩).elim⟩
  obtain ⟨x, hx⟩ := ex
  have h := project_card_of_unique_double F x hx
  omega

/-- In an eight-coordinate cube the projection therefore includes a
direction edge for every coordinate, with both endpoint lifts in the interval. -/
theorem critical_projection_has_direction {ι : Type*} [DecidableEq ι]
    (U : Finset ι) (w : ι → ℝ) (c M : ℝ) (F : Finset (Finset ι × Bool))
    (hU : U.card = 8)
    (hbase : Set.InjOn (slabScore w) {S : Finset ι | S ⊆ U})
    (hm : ∀ (S : Finset ι) (b : Bool), (S, b) ∈ F ↔
      S ⊆ U ∧ c ≤ liftScore M (slabScore w S) b ∧ liftScore M (slabScore w S) b ≤ c + M)
    (hcard : F.card = 149) (i : ι) (hi : i ∈ U) :
    ∃ (S : Finset ι) (a b : Bool), i ∉ S ∧ (S, a) ∈ F ∧ (insert i S, b) ∈ F := by
  classical
  let P := F.image Prod.fst
  have lift (S : Finset ι) (hS : S ∈ P) : ∃ b, (S, b) ∈ F := by
    obtain ⟨⟨T, b⟩, hT, he⟩ := Finset.mem_image.mp hS
    change T = S at he
    subst T
    exact ⟨b, hT⟩
  have hsub : ∀ S ∈ P, S ⊆ U := by
    intro S hS
    obtain ⟨b, hb⟩ := lift S hS
    exact ((hm S b).mp hb).1
  have hlarge : 2 ^ (U.card - 1) < P.card := by
    have h := critical_projection_large U w c M F hbase hm hcard
    change 148 ≤ P.card at h
    rw [hU]
    norm_num
    omega
  obtain ⟨S, hS, hnot, hIns⟩ := directionEdge_of_large_family U P i hi hsub hlarge
  obtain ⟨a, ha⟩ := lift S hS
  obtain ⟨b, hb⟩ := lift (insert i S) hIns
  exact ⟨S, a, b, hnot, ha, hb⟩

#print axioms critical_projection_large
#print axioms critical_projection_has_direction

end NineSeparatedSubsetSums
