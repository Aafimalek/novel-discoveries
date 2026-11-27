import NineSeparatedSubsetSums.ScoreRanking
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Algebra.BigOperators.Fin

open scoped BigOperators

namespace NineSeparatedSubsetSums

/-- Interpret a recursively sliced cube vertex as a Boolean flag on each coordinate. -/
def cubeBitFlags : (n : ℕ) → Cube n ≃ (Fin n → Bool)
  | 0 =>
      { toFun := fun _ i => Fin.elim0 i
        invFun := fun _ => ()
        left_inv := fun x => by cases x; rfl
        right_inv := fun x => by funext i; exact Fin.elim0 i }
  | n + 1 =>
      (Equiv.prodComm (Cube n) Bool).trans <|
        (Equiv.prodCongr (Equiv.refl Bool) (cubeBitFlags n)).trans <|
          Fin.snocEquiv (fun _ : Fin (n + 1) => Bool)

/-- Turning a Boolean membership flag into a finite subset is an equivalence. -/
def flagFinsetEquiv (α : Type*) [Fintype α] [DecidableEq α] : (α → Bool) ≃ Finset α where
  toFun f := Finset.univ.filter (fun i => f i = true)
  invFun A i := decide (i ∈ A)
  left_inv f := by
    funext i
    cases h : f i <;> simp [h]
  right_inv A := by
    ext i
    simp

def cubeFinsetEquiv (n : ℕ) : Cube n ≃ Finset (Fin n) :=
  (cubeBitFlags n).trans (flagFinsetEquiv (Fin n))

def cubeSliceFinsetEquiv (n : ℕ) : Cube (n + 1) ≃ Finset (Fin n) × Bool :=
  Equiv.prodCongr (cubeFinsetEquiv n) (Equiv.refl Bool)

theorem weighted_eq_sum_flags (n : ℕ) (w : Fin n → ℝ) (x : Cube n) :
    weighted n w x = ∑ i, if cubeBitFlags n x i then w i else 0 := by
  induction n with
  | zero => simp [weighted]
  | succ n ih =>
    change Cube n × Bool at x
    obtain ⟨x,b⟩ := x
    change weighted n (fun j => w j.castSucc) x + (if b then w (Fin.last n) else 0) =
      ∑ j, if Fin.snoc (α := fun _ => Bool) (cubeBitFlags n x) b j = true then w j else 0
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.snoc_castSucc, Fin.snoc_last]
    rw [ih]

/-- The computational recursion used by the cube profile is the ordinary
finite subset sum on its corresponding coordinate subset. -/
theorem weighted_eq_sum_cubeFinset (n : ℕ) (w : Fin n → ℝ) (x : Cube n) :
    weighted n w x = ∑ i ∈ cubeFinsetEquiv n x, w i := by
  rw [weighted_eq_sum_flags]
  change (∑ i, if cubeBitFlags n x i then w i else 0) =
    ∑ i ∈ Finset.univ.filter (fun i => cubeBitFlags n x i = true), w i
  rw [Finset.sum_filter]

/-- Cube slicing splits the subset sum into its first n coordinates and
the optional final coordinate. -/
theorem weighted_cubeSlice_symm (n : ℕ) (w : Fin (n + 1) → ℝ)
    (S : Finset (Fin n)) (b : Bool) :
    weighted (n + 1) w ((cubeSliceFinsetEquiv n).symm (S,b)) =
      (∑ i ∈ S, w i.castSucc) + if b then w (Fin.last n) else 0 := by
  change weighted n (fun i => w i.castSucc) ((cubeFinsetEquiv n).symm S)
      + (if b then w (Fin.last n) else 0) =
    (∑ i ∈ S, w i.castSucc) + if b then w (Fin.last n) else 0
  rw [weighted_eq_sum_cubeFinset, Equiv.apply_symm_apply]

/-- The natural separation hypothesis about all pairs of coordinate
subsets supplies an actual rank model on the recursive cube. -/
noncomputable def actualSubsetCubeRankModel (w : Fin 9 → ℝ)
    (sep : ∀ A B : Finset (Fin 9), A ≠ B →
      1 ≤ |(∑ i ∈ A, w i) - (∑ i ∈ B, w i)|) :
    SortedScoreModel (weighted 9 w) 512 :=
  weightedCubeRankModel w (fun x y h => by
    rw [weighted_eq_sum_cubeFinset, weighted_eq_sum_cubeFinset]
    exact sep _ _ (fun h' => h ((cubeFinsetEquiv 9).injective h')))

/-- Transport this rank model to the Finset×Bool view used by the
critical-block formalization without changing its order or rank scores. -/
theorem actualSubsetCubeRank_sliced (w : Fin 9 → ℝ)
    (sep : ∀ A B : Finset (Fin 9), A ≠ B →
      1 ≤ |(∑ i ∈ A, w i) - (∑ i ∈ B, w i)|) :
    ∃ (r : Cube 9 ≃ Fin 512) (v : ℕ → ℝ),
      (∀ x, v (r x).val = weighted 9 w x) ∧
      StrictMono (fun i : Fin 512 => v i.val) ∧
      (∀ i : ℕ, i + 1 < 512 → 1 ≤ v (i + 1) - v i) ∧
      (∀ (S : Finset (Fin 8)) (b : Bool),
        v (((cubeSliceFinsetEquiv 8).symm.trans r) (S,b)).val =
          (∑ i ∈ S, w i.castSucc) + if b then w (Fin.last 8) else 0) := by
  let m := actualSubsetCubeRankModel w sep
  refine ⟨m.rank, m.value, m.lookup, m.increasing, m.gap, ?_⟩
  intro S b
  change m.value (m.rank ((cubeSliceFinsetEquiv 8).symm (S,b))).val = _
  exact (m.lookup _).trans (weighted_cubeSlice_symm 8 w S b)

#print axioms cubeFinsetEquiv
#print axioms weighted_eq_sum_cubeFinset
#print axioms weighted_cubeSlice_symm
#print axioms actualSubsetCubeRankModel
#print axioms actualSubsetCubeRank_sliced

end NineSeparatedSubsetSums
