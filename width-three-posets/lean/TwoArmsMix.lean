import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fin.VecNotation

namespace TwoArmsMix
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000

/-- Labels: 0=b, 1=x, 2=X, 3=y, 4=Y, 5=a. Values are ranks, indexed by labels. -/
def branchRank (p : Fin 6) (u : Fin 6) : ℕ :=
  ![![0,1,2,3,4,5], ![0,1,3,2,4,5], ![0,1,4,2,3,5],
    ![0,2,3,1,4,5], ![0,2,4,1,3,5], ![0,3,4,1,2,5]] p u

def rank (p j u : Fin 6) : ℕ :=
  if u = 5 then j.val else branchRank p u + if j.val ≤ branchRank p u then 1 else 0

/-- Number of cuts up through k displaying u before v in branch order p. -/
def component (p k u v : Fin 6) : ℕ :=
  if u = 5 then
    if v = 5 then 0 else min (k.val + 1) (branchRank p v + 1)
  else if v = 5 then
    k.val + 1 - min (k.val + 1) (branchRank p u + 1)
  else if branchRank p u < branchRank p v then k.val + 1 else 0

abbrev Weights := Fin 6 → Fin 6 → ℕ

def mass (w : Weights) : ℕ := ∑ p : Fin 6, ∑ k : Fin 6, (k.val+1)*w p k

def count (w : Weights) (u v : Fin 6) : ℕ :=
  ∑ p : Fin 6, ∑ k : Fin 6, component p k u v * w p k

/-- Retrieve the linear inequality justified by bounded multiplicities
in every cutoff component. -/
theorem upTo (w : Weights) (a b c : ℕ) (u v x y : Fin 6)
    (h : ∀ p k : Fin 6, a * component p k u v + b * component p k x y ≤ c * (k.val+1)) :
    a * count w u v + b * count w x y ≤ c * mass w := by
  unfold mass count
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro p _
  apply Finset.sum_le_sum
  intro k _
  simpa only [Nat.add_mul, Nat.mul_assoc] using Nat.mul_le_mul_right (w p k) (h p k)

theorem upTo3 (w : Weights) (a b c d e : ℕ) (u v x y z t : Fin 6)
    (h : ∀ p k : Fin 6, a * component p k u v + b * component p k x y +
      c * component p k z t ≤ d * (k.val+1) + e) :
    a * count w u v + b * count w x y + c * count w z t ≤ d * mass w + e * count w 5 0 := by
  have base : ∀ p k : Fin 6, component p k 5 0 = 1 := by decide
  unfold mass count
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib, base]
  apply Finset.sum_le_sum
  intro p _
  apply Finset.sum_le_sum
  intro k _
  simpa only [Nat.add_mul, Nat.mul_assoc, Nat.mul_one, Nat.one_mul] using Nat.mul_le_mul_right (w p k) (h p k)

def Majority (w : Weights) (u v : Fin 6) : Prop := 2 * mass w < 3 * count w u v

def Balanced (w : Weights) (u v : Fin 6) : Prop := u ≠ v ∧
    mass w ≤ 3 * count w u v ∧ 3 * count w u v ≤ 2 * mass w

private theorem complement (w : Weights) {u v : Fin 6} (hne : u ≠ v) :
    count w u v + count w v u = mass w := by
  have aux : ∀ p k x y : Fin 6, x ≠ y →
      component p k x y + component p k y x = k.val + 1 := by decide
  unfold count mass
  simp only [← Finset.sum_add_distrib, ← Nat.add_mul, aux _ _ _ _ hne]

private theorem triangle (w : Weights) (u v z : Fin 6) :
    count w u v + count w v z + count w z u ≤ 2 * mass w := by
  have aux : ∀ p k x y z : Fin 6,
      component p k x y + component p k y z + component p k z x ≤ 2 * (k.val + 1) := by decide
  unfold count mass
  simp only [← Finset.sum_add_distrib, ← Nat.add_mul, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p _
  apply Finset.sum_le_sum
  intro k _
  simpa only [Nat.mul_assoc] using Nat.mul_le_mul_right (w p k) (aux p k u v z)

private theorem majority_total (w : Weights) (hn : ¬ ∃ u v, Balanced w u v)
    {u v : Fin 6} (hne : u ≠ v) : Majority w u v ∨ Majority w v u := by
  have hcomp := complement w hne
  have hf : ¬ (mass w ≤ 3 * count w u v ∧ 3 * count w u v ≤ 2 * mass w) :=
    fun h => hn ⟨u, v, hne, h⟩
  unfold Majority
  omega

private theorem majority_trans (w : Weights) (hn : ¬ ∃ u v, Balanced w u v)
    {u v z : Fin 6} (huz : u ≠ z) (huv : Majority w u v) (hvz : Majority w v z) :
    Majority w u z := by
  rcases majority_total w hn huz with h | h
  · exact h
  · have ht := triangle w u v z
    simp only [Majority] at *
    omega

private theorem fixed (w : Weights) {u v : Fin 6}
    (h : ∀ p k : Fin 6, component p k u v = k.val+1) : count w u v = mass w := by
  unfold count mass
  simp only [h]

/-- Every monotone-cut mixture of the six orders on two disjoint two-element
arms has a balanced comparison when the leading comparison has mass at most one quarter.
The finitely checked per-component inequalities are recorded explicitly. -/
theorem balanced_quarter (w : Weights) (hcap : 4 * count w 5 0 ≤ mass w) :
    ∃ u v, Balanced w u v := by
  by_contra hn
  have tot (u v : Fin 6) (h : u ≠ v) := majority_total w hn h
  have trans (u v z : Fin 6) (h : u ≠ z) := @majority_trans w hn u v z h
  have hpos : 0 < mass w := by
    by_contra! hz
    exact hn ⟨0, 1, by decide, by have h := fixed w (u := 0) (v := 1) (by decide); omega⟩
  have rail1 : Majority w 1 2 := by
    have h := fixed w (u := 1) (v := 2) (by decide)
    unfold Majority
    omega
  have rail2 : Majority w 3 4 := by
    have h := fixed w (u := 3) (v := 4) (by decide)
    unfold Majority
    omega
  rcases tot 1 3 (by decide) with h13 | h31
  ·
    rcases tot 2 3 (by decide) with h23 | h32
    ·
      rcases tot 5 1 (by decide) with t51 | t15
      ·
        have maj51 : Majority w 5 1 := t51
        have maj23 : Majority w 2 3 := h23
        have cert := upTo3 w 2 1 0 1 4 5 1 2 3 0 1 (by decide)
        unfold Majority at maj51
        unfold Majority at maj23
        omega
      ·
        rcases tot 5 2 (by decide) with t52 | t25
        ·
          have maj15 : Majority w 1 5 := t15
          have maj52 : Majority w 5 2 := t52
          have maj53 : Majority w 5 3 := (trans 5 2 3 (by decide) t52 h23)
          have cert := upTo3 w 11 2 4 11 0 1 5 5 2 5 3 (by decide)
          unfold Majority at maj15
          unfold Majority at maj52
          unfold Majority at maj53
          omega
        ·
          rcases tot 5 3 (by decide) with t53 | t35
          ·
            have maj25 : Majority w 2 5 := t25
            have cert := upTo3 w 2 0 0 1 0 2 5 0 1 0 1 (by decide)
            unfold Majority at maj25
            omega
          ·
            rcases tot 5 4 (by decide) with t54 | t45
            ·
              have maj25 : Majority w 2 5 := t25
              have maj35 : Majority w 3 5 := t35
              have cert := upTo3 w 6 3 0 4 0 2 5 3 5 0 1 (by decide)
              unfold Majority at maj25
              unfold Majority at maj35
              omega
            ·
              have maj25 : Majority w 2 5 := t25
              have maj45 : Majority w 4 5 := t45
              have cert := upTo3 w 3 3 0 2 0 2 5 4 5 0 1 (by decide)
              unfold Majority at maj25
              unfold Majority at maj45
              omega
    ·
      rcases tot 2 4 (by decide) with h24 | h42
      ·
        rcases tot 5 1 (by decide) with t51 | t15
        ·
          have maj51 : Majority w 5 1 := t51
          have maj13 : Majority w 1 3 := h13
          have maj24 : Majority w 2 4 := h24
          have cert := upTo3 w 6 2 1 3 12 5 1 1 3 2 4 (by decide)
          unfold Majority at maj51
          unfold Majority at maj13
          unfold Majority at maj24
          omega
        ·
          rcases tot 5 3 (by decide) with t53 | t35
          ·
            have maj15 : Majority w 1 5 := t15
            have maj53 : Majority w 5 3 := t53
            have maj32 : Majority w 3 2 := h32
            have cert := upTo3 w 12 6 1 12 0 1 5 5 3 3 2 (by decide)
            unfold Majority at maj15
            unfold Majority at maj53
            unfold Majority at maj32
            omega
          ·
            rcases tot 5 2 (by decide) with t52 | t25
            ·
              have maj35 : Majority w 3 5 := t35
              have maj13 : Majority w 1 3 := h13
              have cert := upTo3 w 6 1 0 4 0 3 5 1 3 0 1 (by decide)
              unfold Majority at maj35
              unfold Majority at maj13
              omega
            ·
              rcases tot 5 4 (by decide) with t54 | t45
              ·
                have maj25 : Majority w 2 5 := t25
                have maj32 : Majority w 3 2 := h32
                have cert := upTo3 w 6 1 0 3 0 2 5 3 2 0 1 (by decide)
                unfold Majority at maj25
                unfold Majority at maj32
                omega
              ·
                have maj25 : Majority w 2 5 := t25
                have maj45 : Majority w 4 5 := t45
                have cert := upTo3 w 3 3 0 2 0 2 5 4 5 0 1 (by decide)
                unfold Majority at maj25
                unfold Majority at maj45
                omega
      ·
        rcases tot 5 1 (by decide) with t51 | t15
        ·
          have maj51 : Majority w 5 1 := t51
          have maj13 : Majority w 1 3 := h13
          have cert := upTo3 w 2 1 0 1 4 5 1 1 3 0 1 (by decide)
          unfold Majority at maj51
          unfold Majority at maj13
          omega
        ·
          rcases tot 5 3 (by decide) with t53 | t35
          ·
            have maj15 : Majority w 1 5 := t15
            have maj53 : Majority w 5 3 := t53
            have maj32 : Majority w 3 2 := h32
            have cert := upTo3 w 12 6 1 12 0 1 5 5 3 3 2 (by decide)
            unfold Majority at maj15
            unfold Majority at maj53
            unfold Majority at maj32
            omega
          ·
            rcases tot 5 4 (by decide) with t54 | t45
            ·
              have maj35 : Majority w 3 5 := t35
              have maj13 : Majority w 1 3 := h13
              have cert := upTo3 w 6 1 0 4 0 3 5 1 3 0 1 (by decide)
              unfold Majority at maj35
              unfold Majority at maj13
              omega
            ·
              rcases tot 5 2 (by decide) with t52 | t25
              ·
                have maj45 : Majority w 4 5 := t45
                have maj13 : Majority w 1 3 := h13
                have cert := upTo3 w 6 1 0 3 0 4 5 1 3 0 1 (by decide)
                unfold Majority at maj45
                unfold Majority at maj13
                omega
              ·
                have maj25 : Majority w 2 5 := t25
                have maj45 : Majority w 4 5 := t45
                have cert := upTo3 w 3 3 0 2 0 2 5 4 5 0 1 (by decide)
                unfold Majority at maj25
                unfold Majority at maj45
                omega
  ·
    rcases tot 4 1 (by decide) with h41 | h14
    ·
      rcases tot 5 3 (by decide) with t53 | t35
      ·
        have maj53 : Majority w 5 3 := t53
        have maj31 : Majority w 3 1 := h31
        have maj42 : Majority w 4 2 := (trans 4 1 2 (by decide) h41 rail1)
        have cert := upTo3 w 6 2 1 3 12 5 3 3 1 4 2 (by decide)
        unfold Majority at maj53
        unfold Majority at maj31
        unfold Majority at maj42
        omega
      ·
        rcases tot 5 4 (by decide) with t54 | t45
        ·
          have maj51 : Majority w 5 1 := (trans 5 4 1 (by decide) t54 h41)
          have maj35 : Majority w 3 5 := t35
          have maj54 : Majority w 5 4 := t54
          have cert := upTo3 w 4 11 2 11 0 5 1 3 5 5 4 (by decide)
          unfold Majority at maj51
          unfold Majority at maj35
          unfold Majority at maj54
          omega
        ·
          rcases tot 5 1 (by decide) with t51 | t15
          ·
            have maj45 : Majority w 4 5 := t45
            have cert := upTo3 w 2 0 0 1 0 4 5 0 1 0 1 (by decide)
            unfold Majority at maj45
            omega
          ·
            rcases tot 5 2 (by decide) with t52 | t25
            ·
              have maj15 : Majority w 1 5 := t15
              have maj45 : Majority w 4 5 := t45
              have cert := upTo3 w 3 6 0 4 0 1 5 4 5 0 1 (by decide)
              unfold Majority at maj15
              unfold Majority at maj45
              omega
            ·
              have maj25 : Majority w 2 5 := t25
              have maj45 : Majority w 4 5 := t45
              have cert := upTo3 w 3 3 0 2 0 2 5 4 5 0 1 (by decide)
              unfold Majority at maj25
              unfold Majority at maj45
              omega
    ·
      rcases tot 4 2 (by decide) with h42 | h24
      ·
        rcases tot 5 3 (by decide) with t53 | t35
        ·
          have maj53 : Majority w 5 3 := t53
          have maj31 : Majority w 3 1 := h31
          have maj42 : Majority w 4 2 := h42
          have cert := upTo3 w 6 2 1 3 12 5 3 3 1 4 2 (by decide)
          unfold Majority at maj53
          unfold Majority at maj31
          unfold Majority at maj42
          omega
        ·
          rcases tot 5 1 (by decide) with t51 | t15
          ·
            have maj51 : Majority w 5 1 := t51
            have maj35 : Majority w 3 5 := t35
            have maj14 : Majority w 1 4 := h14
            have cert := upTo3 w 6 12 1 12 0 5 1 3 5 1 4 (by decide)
            unfold Majority at maj51
            unfold Majority at maj35
            unfold Majority at maj14
            omega
          ·
            rcases tot 5 4 (by decide) with t54 | t45
            ·
              have maj15 : Majority w 1 5 := t15
              have maj31 : Majority w 3 1 := h31
              have cert := upTo3 w 6 1 0 4 0 1 5 3 1 0 1 (by decide)
              unfold Majority at maj15
              unfold Majority at maj31
              omega
            ·
              rcases tot 5 2 (by decide) with t52 | t25
              ·
                have maj45 : Majority w 4 5 := t45
                have maj14 : Majority w 1 4 := h14
                have cert := upTo3 w 6 1 0 3 0 4 5 1 4 0 1 (by decide)
                unfold Majority at maj45
                unfold Majority at maj14
                omega
              ·
                have maj25 : Majority w 2 5 := t25
                have maj45 : Majority w 4 5 := t45
                have cert := upTo3 w 3 3 0 2 0 2 5 4 5 0 1 (by decide)
                unfold Majority at maj25
                unfold Majority at maj45
                omega
      ·
        rcases tot 5 3 (by decide) with t53 | t35
        ·
          have maj53 : Majority w 5 3 := t53
          have maj31 : Majority w 3 1 := h31
          have maj32 : Majority w 3 2 := (trans 3 1 2 (by decide) h31 rail1)
          have cert := upTo3 w 6 2 1 3 12 5 3 3 1 3 2 (by decide)
          unfold Majority at maj53
          unfold Majority at maj31
          unfold Majority at maj32
          omega
        ·
          rcases tot 5 1 (by decide) with t51 | t15
          ·
            have maj51 : Majority w 5 1 := t51
            have maj35 : Majority w 3 5 := t35
            have maj14 : Majority w 1 4 := h14
            have cert := upTo3 w 6 12 1 12 0 5 1 3 5 1 4 (by decide)
            unfold Majority at maj51
            unfold Majority at maj35
            unfold Majority at maj14
            omega
          ·
            rcases tot 5 2 (by decide) with t52 | t25
            ·
              have maj15 : Majority w 1 5 := t15
              have maj31 : Majority w 3 1 := h31
              have cert := upTo3 w 6 1 0 4 0 1 5 3 1 0 1 (by decide)
              unfold Majority at maj15
              unfold Majority at maj31
              omega
            ·
              rcases tot 5 4 (by decide) with t54 | t45
              ·
                have maj25 : Majority w 2 5 := t25
                have maj31 : Majority w 3 1 := h31
                have cert := upTo3 w 6 1 0 3 0 2 5 3 1 0 1 (by decide)
                unfold Majority at maj25
                unfold Majority at maj31
                omega
              ·
                have maj25 : Majority w 2 5 := t25
                have maj45 : Majority w 4 5 := t45
                have cert := upTo3 w 3 3 0 2 0 2 5 4 5 0 1 (by decide)
                unfold Majority at maj25
                unfold Majority at maj45
                omega

#print axioms balanced_quarter

/-- A mixture at 5/18 demonstrates that the unconstrained monotone-cut
model alone cannot reach that threshold for intertwined branches. -/
def obstruction : Weights := fun p k =>
  if p = 0 && k = 1 then 6 else if p = 0 && k = 3 then 16 else
    if p = 5 && k = 3 then 8 else 0

theorem obstruction_check : 18 * count obstruction 5 0 = 5 * mass obstruction ∧
    ¬ ∃ u v, Balanced obstruction u v := by
  change 18 * count obstruction 5 0 = 5 * mass obstruction ∧
    ¬ ∃ u v : Fin 6, u ≠ v ∧ mass obstruction ≤ 3 * count obstruction u v ∧
      3 * count obstruction u v ≤ 2 * mass obstruction
  decide

#print axioms obstruction_check

end TwoArmsMix
