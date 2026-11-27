import LatinGap

namespace LatinGap
open Finset

/-- Permute coordinate roles, and independently relabel each new coordinate.
The coordinate permutation sends each new index to its old index. -/
def renameWords {n : ℕ} (idx : Coord ≃ Coord) (lab : Coord → Fin n ≃ Fin n) :
    Word n ≃ Word n where
  toFun w i := lab i (w (idx i))
  invFun w i := (lab (idx.symm i)).symm (w (idx.symm i))
  left_inv w := by funext i; simp
  right_inv w := by funext i; simp

def renameDesign {n : ℕ} (idx : Coord ≃ Coord) (lab : Coord → Fin n ≃ Fin n)
    (D : Design n) : Design n :=
  D.map (renameWords idx lab).toEmbedding

theorem renameDesign_card {n : ℕ} (idx : Coord ≃ Coord) (lab : Coord → Fin n ≃ Fin n)
    (D : Design n) : (renameDesign idx lab D).card = D.card := Finset.card_map _

theorem renameDesign_linear {n : ℕ} {D : Design n} (hD : Linear D)
    (idx : Coord ≃ Coord) (lab : Coord → Fin n ≃ Fin n) :
    Linear (renameDesign idx lab D) := by
  intro u hu v hv i j hij hi hj
  obtain ⟨a,ha,rfl⟩ := Finset.mem_map.mp hu
  obtain ⟨b,hb,rfl⟩ := Finset.mem_map.mp hv
  change lab i (a (idx i)) = lab i (b (idx i)) at hi
  change lab j (a (idx j)) = lab j (b (idx j)) at hj
  rw [hD ha hb (idx.injective.ne hij) ((lab i).injective hi) ((lab j).injective hj)]

theorem renameDesign_saturated {n : ℕ} {D : Design n} (hD : Saturated D)
    (idx : Coord ≃ Coord) (lab : Coord → Fin n ≃ Fin n) :
    Saturated (renameDesign idx lab D) := by
  intro w
  let e := renameWords idx lab
  obtain ⟨i,j,hij,u,hu,hi,hj⟩ := hD (e.symm w)
  refine ⟨idx.symm i,idx.symm j,idx.symm.injective.ne hij,e u,?_,?_,?_⟩
  · exact Finset.mem_map.mpr ⟨u,hu,rfl⟩
  · change lab (idx.symm i) (u (idx (idx.symm i))) = w (idx.symm i)
    rw [idx.apply_symm_apply,hi]
    change lab (idx.symm i) ((lab (idx.symm i)).symm (w (idx.symm i))) = _
    exact (lab (idx.symm i)).apply_symm_apply _
  · change lab (idx.symm j) (u (idx (idx.symm j))) = w (idx.symm j)
    rw [idx.apply_symm_apply,hj]
    change lab (idx.symm j) ((lab (idx.symm j)).symm (w (idx.symm j))) = _
    exact (lab (idx.symm j)).apply_symm_apply _

theorem renameDesign_freq {n : ℕ} (idx : Coord ≃ Coord) (lab : Coord → Fin n ≃ Fin n)
    (D : Design n) (i : Coord) (a : Fin n) :
    freq (renameDesign idx lab D) (i,lab i a) = freq D (idx i,a) := by
  have e : incident (renameDesign idx lab D) (i,lab i a) =
      (incident D (idx i,a)).map (renameWords idx lab).toEmbedding := by
    ext w
    constructor
    · intro hw
      obtain ⟨hwD,hwi⟩ := Finset.mem_filter.mp hw
      obtain ⟨u,hu,rfl⟩ := Finset.mem_map.mp hwD
      change lab i (u (idx i)) = lab i a at hwi
      exact Finset.mem_map.mpr ⟨u,Finset.mem_filter.mpr ⟨hu,(lab i).injective hwi⟩,rfl⟩
    · intro hw
      obtain ⟨u,hu,rfl⟩ := Finset.mem_map.mp hw
      obtain ⟨huD,hui⟩ := Finset.mem_filter.mp hu
      refine Finset.mem_filter.mpr ⟨Finset.mem_map.mpr ⟨u,huD,rfl⟩,?_⟩
      change lab i (u (idx i)) = lab i a
      exact congrArg (lab i) hui
  unfold freq
  rw [e,Finset.card_map]

/-- The elementary common normalization: put any minimum-degree label
at (0,0), preserving linearity, saturation, size and minimum degree.
This does not yet impose the further normalized incident-word patterns. -/
theorem normalize_min_label_six {D : Design 6} (hD : Linear D) (hS : Saturated D)
    (x : Label 6) (m : ℕ) (hmin : ∀ y : Label 6, m ≤ freq D y) (hx : freq D x = m) :
    ∃ E : Design 6, Linear E ∧ Saturated E ∧ E.card = D.card ∧
      (∀ y : Label 6, m ≤ freq E y) ∧ freq E (0,0) = m := by
  let idx : Coord ≃ Coord := Equiv.swap 0 x.1
  let lab : Coord → Fin 6 ≃ Fin 6 := fun i => if i = 0 then Equiv.swap x.2 0 else Equiv.refl _
  let E := renameDesign idx lab D
  refine ⟨E,renameDesign_linear hD _ _,renameDesign_saturated hS _ _,renameDesign_card _ _ _,?_,?_⟩
  · rintro ⟨i,a⟩
    have he := renameDesign_freq idx lab D i ((lab i).symm a)
    rw [(lab i).apply_symm_apply] at he
    exact he.symm ▸ hmin (idx i,(lab i).symm a)
  · have he := renameDesign_freq idx lab D 0 x.2
    have hi : idx 0 = x.1 := Equiv.swap_apply_left _ _
    have ha : lab 0 x.2 = 0 := by simp [lab]
    rw [hi,ha] at he
    exact he.trans hx

#print axioms renameDesign_linear
#print axioms renameDesign_saturated
#print axioms renameDesign_freq
#print axioms normalize_min_label_six
end LatinGap
