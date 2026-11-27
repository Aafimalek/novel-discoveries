import Mathlib

namespace NineSeparatedSubsetSums

/-- A cube written recursively so the last coordinate gives two slices. -/
def Cube : ℕ → Type
  | 0 => Unit
  | n + 1 => Cube n × Bool

instance cubeDecidableEq (n : ℕ) : DecidableEq (Cube n) := by
  induction n with
  | zero => change DecidableEq Unit; infer_instance
  | succ n ih =>
      letI : DecidableEq (Cube n) := ih
      change DecidableEq (Cube n × Bool)
      infer_instance

instance cubeFintype (n : ℕ) : Fintype (Cube n) := by
  induction n with
  | zero => change Fintype Unit; infer_instance
  | succ n ih =>
      letI : Fintype (Cube n) := ih
      change Fintype (Cube n × Bool)
      infer_instance

theorem cube_card (n : ℕ) : Fintype.card (Cube n) = 2 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change Fintype.card (Cube n × Bool) = 2 ^ (n + 1)
      rw [Fintype.card_prod, ih]
      simp [pow_succ]

/-- Equality or a change in exactly one coordinate. -/
def near : (n : ℕ) → Cube n → Cube n → Prop
  | 0, _, _ => True
  | n + 1, (x, b), (y, c) => (b = c ∧ near n x y) ∨ x = y

noncomputable def closed (n : ℕ) (A : Finset (Cube n)) : Finset (Cube n) := by
  classical
  exact Finset.univ.filter (fun x => ∃ y ∈ A, near n x y)

theorem mem_closed {n : ℕ} {A : Finset (Cube n)} {x : Cube n} :
    x ∈ closed n A ↔ ∃ y ∈ A, near n x y := by
  classical
  simp [closed]

noncomputable def slice (n : ℕ) (A : Finset (Cube (n + 1))) (b : Bool) : Finset (Cube n) := by
  classical
  exact Finset.univ.filter (fun x : Cube n => ((x, b) : Cube (n + 1)) ∈ A)

theorem mem_slice {n : ℕ} {A : Finset (Cube (n + 1))} {b : Bool} {x : Cube n} :
    x ∈ slice n A b ↔ ((x, b) : Cube (n + 1)) ∈ A := by
  simp [slice]

def embed (n : ℕ) (b : Bool) : Cube n ↪ Cube (n + 1) :=
  ⟨fun x => (x, b), fun _ _ h => congrArg Prod.fst h⟩

theorem card_slices (n : ℕ) (A : Finset (Cube (n + 1))) :
    A.card = (slice n A false).card + (slice n A true).card := by
  let A₀ := (slice n A false).map (embed n false)
  let A₁ := (slice n A true).map (embed n true)
  have hU : A₀ ∪ A₁ = A := by
    ext p
    change p ∈ A₀ ∪ A₁ ↔ p ∈ A
    change Cube n × Bool at p
    obtain ⟨x, b⟩ := p
    have hm (i : Bool) :
        ((x, b) : Cube (n + 1)) ∈ (slice n A i).map (embed n i) ↔
          b = i ∧ ((x, b) : Cube (n + 1)) ∈ A := by
      constructor
      · intro h
        obtain ⟨y, hy, he⟩ := Finset.mem_map.mp h
        have hxy : y = x := congrArg Prod.fst he
        have hib : i = b := congrArg Prod.snd he
        subst y
        subst i
        exact ⟨rfl, mem_slice.mp hy⟩
      · rintro ⟨rfl, h⟩
        exact Finset.mem_map.mpr ⟨x, mem_slice.mpr h, rfl⟩
    change ((x, b) : Cube (n + 1)) ∈ A₀ ∪ A₁ ↔ _
    rw [Finset.mem_union, hm false, hm true]
    cases b <;> simp
  have hd : Disjoint A₀ A₁ := by
    refine Finset.disjoint_left.mpr ?_
    intro p hp hq
    obtain ⟨x, _, hx⟩ := Finset.mem_map.mp hp
    obtain ⟨y, _, hy⟩ := Finset.mem_map.mp hq
    have heq : ((x, false) : Cube (n + 1)) = (y, true) := hx.trans hy.symm
    have hf : false = true := congrArg Prod.snd heq
    cases hf
  calc
    A.card = (A₀ ∪ A₁).card := congrArg Finset.card hU.symm
    _ = A₀.card + A₁.card := Finset.card_union_of_disjoint hd
    _ = (slice n A false).card + (slice n A true).card := by simp [A₀, A₁]

theorem same_slice (n : ℕ) (A : Finset (Cube (n + 1))) (b : Bool) :
    closed n (slice n A b) ⊆ slice n (closed (n + 1) A) b := by
  intro x hx
  obtain ⟨y, hy, hxy⟩ := mem_closed.mp hx
  exact mem_slice.mpr (mem_closed.mpr ⟨(y, b), mem_slice.mp hy, Or.inl ⟨rfl, hxy⟩⟩)

theorem other_slice (n : ℕ) (A : Finset (Cube (n + 1))) (b : Bool) :
    slice n A (!b) ⊆ slice n (closed (n + 1) A) b := by
  intro x hx
  exact mem_slice.mpr (mem_closed.mpr ⟨(x, !b), mem_slice.mp hx, Or.inr rfl⟩)

/-- Every numeric profile satisfying the two-slice recurrence is a lower
bound on the size of the closed neighborhood in the next dimension. -/
theorem profile_step (n : ℕ) (g f : ℕ → ℕ)
    (hg : ∀ A : Finset (Cube n), g A.card ≤ (closed n A).card)
    (hf : ∀ a b : ℕ, a ≤ 2 ^ n → b ≤ 2 ^ n →
      f (a + b) ≤ max (g a) b + max (g b) a)
    (A : Finset (Cube (n + 1))) :
    f A.card ≤ (closed (n + 1) A).card := by
  let S₀ := slice n A false
  let S₁ := slice n A true
  let T₀ := slice n (closed (n + 1) A) false
  let T₁ := slice n (closed (n + 1) A) true
  have ha : S₀.card ≤ 2 ^ n := by rw [← cube_card]; exact Finset.card_le_univ _
  have hb : S₁.card ≤ 2 ^ n := by rw [← cube_card]; exact Finset.card_le_univ _
  have h₀ : max (g S₀.card) S₁.card ≤ T₀.card :=
    max_le (le_trans (hg S₀) (Finset.card_le_card (same_slice n A false)))
      (Finset.card_le_card (other_slice n A false))
  have h₁ : max (g S₁.card) S₀.card ≤ T₁.card :=
    max_le (le_trans (hg S₁) (Finset.card_le_card (same_slice n A true)))
      (Finset.card_le_card (other_slice n A true))
  calc
    f A.card = f (S₀.card + S₁.card) := congrArg f (card_slices n A)
    _ ≤ max (g S₀.card) S₁.card + max (g S₁.card) S₀.card := hf _ _ ha hb
    _ ≤ T₀.card + T₁.card := Nat.add_le_add h₀ h₁
    _ = (closed (n + 1) A).card := (card_slices n (closed (n + 1) A)).symm

end NineSeparatedSubsetSums
