import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.List.Sublists
import Mathlib.Data.List.Nodup
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Lean.Elab.Tactic.Omega

namespace NineSeparatedSubsetSums

/-- A natural number's 1-bits are exactly the members of this list. The
list can retain multiplicities, which are checked separately by Nodup. -/
def maskRep (s : List ℕ) (m : ℕ) : Prop :=
  ∀ k : ℕ, m.testBit k = true ↔ k ∈ s

theorem maskRep_shift {s : List ℕ} {m : ℕ} (rep : maskRep s m) (a : ℕ) :
    maskRep (s.map (· + a)) (m <<< a) := by
  intro k
  simp only [Nat.testBit_shiftLeft, Bool.and_eq_true, decide_eq_true_eq, rep k, rep (k-a)]
  constructor
  · rintro ⟨h₁,h₂⟩
    exact List.mem_map.mpr ⟨k-a, h₂, by omega⟩
  · intro h
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp h
    exact ⟨by omega, by simpa using hj⟩

theorem maskRep_append {s t : List ℕ} {m n : ℕ}
    (rep₁ : maskRep s m) (rep₂ : maskRep t n) :
    maskRep (s ++ t) (m ||| n) := by
  intro k
  simp only [Nat.testBit_lor, Bool.or_eq_true, List.mem_append, rep₁ k, rep₂ k]

theorem maskRep_disjoint_iff {s t : List ℕ} {m n : ℕ}
    (rep₁ : maskRep s m) (rep₂ : maskRep t n) :
    (m &&& n) = 0 ↔ s.Disjoint t := by
  rw [List.disjoint_left]
  constructor
  · intro h k hs ht
    have hm := (rep₁ k).mpr hs
    have hn := (rep₂ k).mpr ht
    have hz : (m &&& n).testBit k = true := by simp [Nat.testBit_land, hm, hn]
    simpa [h] using hz
  · intro h
    apply Nat.zero_of_testBit_eq_false
    intro k
    rw [Nat.testBit_land]
    cases hm : m.testBit k <;> cases hn : n.testBit k <;> simp
    exact (h ((rep₁ k).mp hm) ((rep₂ k).mp hn)).elim

/-- Sum of the weights of each of the sublists obtained by positional
subset choices, in the order used by `List.sublists`. -/
def natSubsetSums (weights : List ℕ) : List ℕ :=
  weights.sublists.map List.sum

theorem natSubsetSums_snoc (weights : List ℕ) (a : ℕ) :
    natSubsetSums (weights ++ [a]) =
      natSubsetSums weights ++ (natSubsetSums weights).map (· + a) := by
  simp [natSubsetSums, List.sublists_concat, List.sum_append, List.map_map, Function.comp_def]

/-- The bitset storage update after a valid weight addition. -/
def addSubsetMask (m a : ℕ) : ℕ := m ||| (m <<< a)

theorem addSubsetMask_represents (weights : List ℕ) (a m : ℕ)
    (rep : maskRep (natSubsetSums weights) m) :
    maskRep (natSubsetSums (weights ++ [a])) (addSubsetMask m a) := by
  rw [natSubsetSums_snoc]
  exact maskRep_append rep (maskRep_shift rep a)

/-- The zero-overlap guard is exactly the no-collision test for the two
translations, provided the old subset sums were already distinct. -/
theorem addSubsetMask_collision_iff (weights : List ℕ) (a m : ℕ)
    (rep : maskRep (natSubsetSums weights) m)
    (old : (natSubsetSums weights).Nodup) :
    (m &&& (m <<< a)) = 0 ↔ (natSubsetSums (weights ++ [a])).Nodup := by
  rw [natSubsetSums_snoc, List.nodup_append']
  rw [maskRep_disjoint_iff rep (maskRep_shift rep a)]
  have mapNodup : ((natSubsetSums weights).map (· + a)).Nodup :=
    old.map (fun _ _ h => Nat.add_right_cancel h)
  simp [old, mapNodup]

/-- Extend the validated-search state. The Boolean remembers any earlier
collision even if its witnesses have merged into the mask support. -/
def addMaskState (st : ℕ × Bool) (a : ℕ) : ℕ × Bool :=
  (addSubsetMask st.1 a, st.2 && decide ((st.1 &&& (st.1 <<< a)) = 0))

def computeSubsetMask (weights : List ℕ) : ℕ × Bool :=
  weights.foldl addMaskState (1,true)

theorem computeSubsetMask_correct (weights : List ℕ) :
    maskRep (natSubsetSums weights) (computeSubsetMask weights).1 ∧
    ((computeSubsetMask weights).2 = true ↔ (natSubsetSums weights).Nodup) := by
  refine List.reverseRecOn weights ?_ (fun ws a ih => ?_)
  · constructor
    · intro k
      change (1 : ℕ).testBit k = true ↔ k ∈ [0]
      rw [Nat.testBit_one_eq_true_iff_self_eq_zero, List.mem_singleton]
    · change true = true ↔ ([0] : List ℕ).Nodup
      simp
  · have hstep : computeSubsetMask (ws ++ [a]) = addMaskState (computeSubsetMask ws) a := by
      simp only [computeSubsetMask, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [hstep]
    refine ⟨addSubsetMask_represents ws a _ ih.1, ?_⟩
    change ((computeSubsetMask ws).2 && decide (((computeSubsetMask ws).1 &&&
      ((computeSubsetMask ws).1 <<< a)) = 0)) = true ↔ (natSubsetSums (ws ++ [a])).Nodup
    rw [Bool.and_eq_true, decide_eq_true_eq, ih.2]
    constructor
    · rintro ⟨old, test⟩
      exact (addSubsetMask_collision_iff ws a _ ih.1 old).mp test
    · intro new
      have old : (natSubsetSums ws).Nodup := by
        rw [natSubsetSums_snoc] at new
        exact new.of_append_left
      exact ⟨old, (addSubsetMask_collision_iff ws a _ ih.1 old).mpr new⟩

/-- Small closed smoke example, kernel-checked without native evaluation. -/
example : (computeSubsetMask [1,2,4,8,16]).2 = true := by decide
example : (computeSubsetMask [1,2,3]).2 = false := by decide

#print axioms maskRep_shift
#print axioms addSubsetMask_represents
#print axioms addSubsetMask_collision_iff
#print axioms computeSubsetMask_correct

end NineSeparatedSubsetSums
