import EulerSequentialCount
import EulerDegreeThreshold
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Logic.Equiv.Fin.Basic

open Finset
open scoped BigOperators

namespace LatinGap.PairEncoding

theorem prefixOnes_as_sum_range (x : ℕ → Bool) (n : ℕ) :
    prefixOnes x n = ∑ i ∈ range n, (if x i then 1 else 0 : ℕ) := by
  induction n with
  | zero => simp [prefixOnes]
  | succ n ih => rw [prefixOnes, Finset.sum_range_succ, ih]

theorem prefixOnes_as_sum_fin (x : ℕ → Bool) (n : ℕ) :
    prefixOnes x n = ∑ i : Fin n, (if x i.val then 1 else 0 : ℕ) := by
  rw [prefixOnes_as_sum_range]
  exact (Fin.sum_univ_eq_sum_range (fun i : ℕ => (if x i then 1 else 0 : ℕ)) n).symm

/-- All pair projections of a linear design have the placement count. -/
theorem geometry_pair_projection_card (D : Design n) (linear : Linear D)
    (i j : Coord) (ne : i ≠ j) : (D.image (fun w => (w i,w j))).card = D.card := by
  apply card_image_of_injOn
  intro u hu v hv e
  exact linear hu hv ne (congrArg Prod.fst e) (congrArg Prod.snd e)

private def firstPair (p : Fin 6 × Fin 6) : PairKey 6 :=
  ⟨0,1,by decide,p.1,p.2⟩

theorem firstPair_number (p : Fin 6 × Fin 6) :
    pairNumber (firstPair p) = 1297 + (finProdFinEquiv p : Fin 36).val := by
  simp [firstPair, pairNumber, coordNumber, finProdFinEquiv, Nat.add_assoc, Nat.add_comm]

/-- The archived contiguous IDs 1297--1332 contain exactly the first
projection of a hypothetical linear 17-placement design. -/
theorem geometry_first_projection_prefixOnes (D : Design 6) (linear : Linear D)
    (size : D.card=17) (v : ℕ → Bool)
    (hpair : ∀ p : PairKey 6, v (pairNumber p) = (encode D).pair p) :
    prefixOnes (fun i => v (1297+i)) 36 = 17 := by
  classical
  have setEq : (univ.filter (fun p : Fin 6×Fin 6 => (encode D).pair (firstPair p) = true)) =
      D.image (fun w => (w 0,w 1)) := by
    ext p
    simp only [mem_filter,mem_univ,true_and,pair_encode,firstPair,Used]
    rw [mem_image]
    constructor
    · rintro ⟨_,w,hw,h₁,h₂⟩
      exact ⟨w,hw,Prod.ext h₁ h₂⟩
    · rintro ⟨w,hw,e⟩
      exact ⟨by decide,w,hw,congrArg Prod.fst e,congrArg Prod.snd e⟩
  rw [prefixOnes_as_sum_fin]
  calc
    (∑ i : Fin 36, (if v (1297+i.val) then 1 else 0 : ℕ)) =
        ∑ p : Fin 6×Fin 6, (if (encode D).pair (firstPair p) then 1 else 0 : ℕ) := by
      symm
      apply Fintype.sum_equiv (finProdFinEquiv : (Fin 6 × Fin 6) ≃ Fin 36)
      intro p
      rw [← firstPair_number, hpair]
    _ = (univ.filter (fun p : Fin 6×Fin 6 => (encode D).pair (firstPair p) = true)).card := by
      rw [card_filter]
    _ = 17 := by rw [setEq,geometry_pair_projection_card D linear 0 1 (by decide),size]

/-- The degree of a six-symbol label in a linear design is at most six. -/
theorem geometry_freq_at_most_six (D : Design 6) (linear : Linear D) (g : Coord) (a : Fin 6) :
    freq D (g,a) ≤ 6 := by
  have h := card_le_univ (s := neighbors D (g,a) (degreePartner g))
  have ne : (g,a).1 ≠ degreePartner g := degreePartner_ne g
  rw [card_neighbors linear ne] at h
  simpa using h

theorem count_high_thresholds (deg : ℕ) (lower : 2≤deg) (upper : deg≤6) :
    (∑ k : Fin 4, (if 3+k.val≤deg then 1 else 0 : ℕ)) = deg-2 := by
  interval_cases deg <;> decide

/-- Sum of the four thresholds 3,4,5,6 over the six labels is precisely
the excess (17-6·2=5) in each group. -/
theorem geometry_degree_excess_sum (D : Design 6) (linear : Linear D)
    (size : D.card=17) (g : Coord) (minimum : ∀ a : Fin 6, 2 ≤ freq D (g,a)) :
    (∑ a : Fin 6, ∑ k : Fin 4,
       (if 3+k.val≤freq D (g,a) then 1 else 0 : ℕ)) = 5 := by
  have row (a : Fin 6) := count_high_thresholds (freq D (g,a)) (minimum a)
    (geometry_freq_at_most_six D linear g a)
  simp_rw [row]
  have co : ∀ a : Fin 6, (freq D (g,a)-2)+2 = freq D (g,a) :=
    fun a => Nat.sub_add_cancel (minimum a)
  have eq : ∑ a : Fin 6, ((freq D (g,a)-2)+2) = ∑ a : Fin 6, freq D (g,a) :=
    Finset.sum_congr rfl (fun a _ => co a)
  rw [sum_add_distrib, sum_freq, size] at eq
  simp at eq
  omega

def degreeExcessInput (v : ℕ → Bool) (g : Coord) (i : ℕ) : Bool :=
  v (degreeThresholdNumber g ⟨(i / 4)%6, by omega⟩ ⟨3+i%4, by omega⟩)

def degreeExcessLevel (k : Fin 4) : Fin 7 := ⟨3+k.val, by have := k.isLt; omega⟩

theorem degreeExcessInput_at_prod (v : ℕ → Bool) (g : Coord) (p : Fin 6×Fin 4) :
    degreeExcessInput v g (finProdFinEquiv p : Fin 24).val =
      v (degreeThresholdNumber g p.1 (degreeExcessLevel p.2)) := by
  have h₁ := p.1.isLt
  have h₂ := p.2.isLt
  have labelEq : (⟨((p.2.val+4*p.1.val)/4)%6, by omega⟩ : Fin 6)=p.1 :=
    Fin.ext (by dsimp; omega)
  have threshEq : (⟨3+(p.2.val+4*p.1.val)%4, by omega⟩ : Fin 7)=degreeExcessLevel p.2 :=
    Fin.ext (by dsimp [degreeExcessLevel]; omega)
  change v (degreeThresholdNumber g ⟨((p.2.val+4*p.1.val)/4)%6, _⟩
      ⟨3+(p.2.val+4*p.1.val)%4,_⟩) = _
  rw [labelEq,threshEq]

theorem geometry_degree_excess_prefixOnes (D : Design 6) (linear : Linear D)
    (size : D.card=17) (g : Coord) (minimum : ∀ a : Fin 6, 2≤freq D (g,a))
    (v : ℕ → Bool)
    (hdeg : ∀ a : Fin 6, ∀ k : Fin 7, v (degreeThresholdNumber g a k) = decide (k.val ≤ freq D (g,a))) :
    prefixOnes (degreeExcessInput v g) 24 = 5 := by
  rw [prefixOnes_as_sum_fin]
  calc
    (∑ i : Fin 24, (if degreeExcessInput v g i.val then 1 else 0 : ℕ)) =
        ∑ p : Fin 6×Fin 4, (if 3+p.2.val≤freq D (g,p.1) then 1 else 0 : ℕ) := by
      symm
      apply Fintype.sum_equiv (finProdFinEquiv : (Fin 6 × Fin 4) ≃ Fin 24)
      intro p
      rw [degreeExcessInput_at_prod,hdeg]
      by_cases h : 3+p.2.val≤freq D (g,p.1) <;> simp [degreeExcessLevel,h]
    _ = 5 := by
      rw [← Finset.univ_product_univ, Finset.sum_product]
      exact geometry_degree_excess_sum D linear size g minimum

/-- Actual geometric pair/degree values can be extended by valid states
of the exact-17 and all four exact-5 sequential counters. -/
theorem geometry_seventeen_counter_states (D : Design 6) (linear : Linear D) (size : D.card=17)
    (minimum : ∀ g : Coord, ∀ a : Fin 6, 2 ≤ freq D (g,a)) (v : ℕ → Bool)
    (hpair : ∀ p : PairKey 6, v (pairNumber p) = (encode D).pair p)
    (hdeg : ∀ g : Coord, ∀ a : Fin 6, ∀ k : Fin 7,
      v (degreeThresholdNumber g a k) = decide (k.val ≤ freq D (g,a))) :
    (∃ z s, SequentialBound 17 19 (fun i => !v (1297+i)) z ∧
      SequentialBound 19 17 (fun i => v (1297+i)) s) ∧
    ∀ g : Coord, ∃ z s, SequentialBound 5 19 (fun i => !degreeExcessInput v g i) z ∧
      SequentialBound 19 5 (degreeExcessInput v g) s := by
  refine ⟨(projection_seventeen_counter_iff _).mpr
    (geometry_first_projection_prefixOnes D linear size v hpair), ?_⟩
  intro g
  exact (degree_excess_five_counter_iff _).mpr
    (geometry_degree_excess_prefixOnes D linear size g (minimum g) v (hdeg g))

#print axioms geometry_first_projection_prefixOnes
#print axioms geometry_degree_excess_prefixOnes
#print axioms geometry_seventeen_counter_states

end LatinGap.PairEncoding
