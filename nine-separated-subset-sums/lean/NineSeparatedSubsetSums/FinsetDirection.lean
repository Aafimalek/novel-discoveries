import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Card
import Lean.Elab.Tactic.Omega

namespace NineSeparatedSubsetSums

/-- More than half a cube must contain an edge in every fixed direction. -/
theorem directionEdge_of_large_family {ι : Type*} [DecidableEq ι]
    (U : Finset ι) (P : Finset (Finset ι)) (i : ι) (hi : i ∈ U)
    (hsub : ∀ S ∈ P, S ⊆ U)
    (hcard : 2 ^ (U.card - 1) < P.card) :
    ∃ S ∈ P, i ∉ S ∧ insert i S ∈ P := by
  classical
  by_contra h
  have hs : P.image (fun s => s.erase i) ⊆ (U.erase i).powerset := by
    intro T ht
    obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp ht
    rw [Finset.mem_powerset]
    intro y hy
    exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hy).1, hsub S hS (Finset.mem_erase.mp hy).2⟩
  have pinj : Set.InjOn (fun s : Finset ι => s.erase i) P := by
    intro S hS T hT e
    change S ∈ P at hS
    change T ∈ P at hT
    change S.erase i = T.erase i at e
    by_cases hiS : i ∈ S <;> by_cases hiT : i ∈ T
    · exact (Finset.insert_erase hiS).symm.trans
        ((congrArg (insert i) e).trans (Finset.insert_erase hiT))
    · rw [Finset.erase_eq_of_notMem hiT] at e
      have hh : insert i T = S := (congrArg (insert i) e.symm).trans (Finset.insert_erase hiS)
      exact (h ⟨T, hT, hiT, hh.symm ▸ hS⟩).elim
    · rw [Finset.erase_eq_of_notMem hiS] at e
      have hh : insert i S = T := (congrArg (insert i) e).trans (Finset.insert_erase hiT)
      exact (h ⟨S, hS, hiS, hh.symm ▸ hT⟩).elim
    · rwa [Finset.erase_eq_of_notMem hiS, Finset.erase_eq_of_notMem hiT] at e
  have hle := Finset.card_le_card hs
  rw [Finset.card_image_of_injOn pinj, Finset.card_powerset, Finset.card_erase_of_mem hi] at hle
  omega

#print axioms directionEdge_of_large_family

end NineSeparatedSubsetSums
