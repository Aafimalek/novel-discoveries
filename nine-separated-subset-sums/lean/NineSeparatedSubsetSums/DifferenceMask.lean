import NineSeparatedSubsetSums.SubsetMask

namespace NineSeparatedSubsetSums

/-- Center D at R: bit k records k = R + x - y for old subset scores.
The natural-number equation avoids truncated-subtraction artifacts. -/
def centeredDiffRep (s : List ℕ) (R D : ℕ) : Prop :=
  ∀ k, D.testBit k = true ↔ ∃ x ∈ s, ∃ y ∈ s, k + y = R + x

def addCenteredDiffMask (D a : ℕ) : ℕ := D ||| (D <<< a) ||| (D <<< (2*a))

/-- Adding a weight translates the difference support by 0, a or 2a
when its center simultaneously grows by a. -/
theorem addCenteredDiffMask_rep {s : List ℕ} {R D : ℕ}
    (rep : centeredDiffRep s R D) (bound : ∀ x ∈ s, x ≤ R) (a : ℕ) :
    centeredDiffRep (s ++ s.map (· + a)) (R+a) (addCenteredDiffMask D a) := by
  intro k
  simp only [addCenteredDiffMask, Nat.testBit_lor, Bool.or_eq_true, Nat.testBit_shiftLeft,
    Bool.and_eq_true, decide_eq_true_eq, rep k, rep (k-a), rep (k-2*a), List.mem_append, List.mem_map]
  constructor
  · rintro ((h | h) | h)
    · obtain ⟨x,hx,y,hy,hxy⟩ := h
      exact ⟨x, Or.inl hx, y+a, Or.inr ⟨y,hy,rfl⟩, by omega⟩
    · obtain ⟨ha,x,hx,y,hy,hxy⟩ := h
      exact ⟨x, Or.inl hx, y, Or.inl hy, by omega⟩
    · obtain ⟨ha,x,hx,y,hy,hxy⟩ := h
      exact ⟨x+a, Or.inr ⟨x,hx,rfl⟩, y, Or.inl hy, by omega⟩
  · rintro ⟨x,hx | ⟨x,hx,rfl⟩,y,hy | ⟨y,hy,rfl⟩,hxy⟩
    · have hyR := bound y hy
      exact Or.inl (Or.inr ⟨by omega,x,hx,y,hy,by omega⟩)
    · exact Or.inl (Or.inl ⟨x,hx,y,hy,by omega⟩)
    · have hyR := bound y hy
      exact Or.inr ⟨by omega,x,hx,y,hy,by omega⟩
    · have hyR := bound y hy
      exact Or.inl (Or.inr ⟨by omega,x,hx,y,hy,by omega⟩)

theorem centeredDiff_snoc_nodup_iff {s : List ℕ} {R D : ℕ}
    (rep : centeredDiffRep s R D) (old : s.Nodup) (a : ℕ) :
    (s ++ s.map (· + a)).Nodup ↔ D.testBit (R+a) = false := by
  constructor
  · intro nd
    cases h : D.testBit (R+a) with
    | false => rfl
    | true =>
      obtain ⟨x,hx,y,hy,he⟩ := (rep _).mp h
      have hm : x ∈ s.map (· + a) := List.mem_map.mpr ⟨y,hy,by omega⟩
      exact (List.disjoint_left.mp nd.disjoint hx hm).elim
  · intro miss
    apply old.append (old.map (fun _ _ e => Nat.add_right_cancel e))
    rw [List.disjoint_left]
    intro x hx hm
    obtain ⟨y,hy,he⟩ := List.mem_map.mp hm
    have hit := (rep (R+a)).mpr ⟨x,hx,y,hy,by omega⟩
    simp [miss] at hit

/-- When a is held fixed, all forbidden second additions can be collected
in one OR of shifts of the old difference mask. -/
def forbiddenTailMask (D R a : ℕ) : ℕ :=
  (D >>> R) ||| (D >>> (R+a)) ||| (D >>> (R-a))

theorem forbiddenTailMask_testBit {D R a : ℕ} (leR : a ≤ R) (b : ℕ) :
    (addCenteredDiffMask D a).testBit (R+a+b) =
      (forbiddenTailMask D R a).testBit b := by
  have ha₁ : a ≤ R+a+b := by omega
  have ha₂ : 2*a ≤ R+a+b := by omega
  have he₁ : R+a+b-a = R+b := by omega
  have he₂ : R+a+b-2*a = R-a+b := by omega
  simp only [addCenteredDiffMask, forbiddenTailMask, Nat.testBit_lor,
    Nat.testBit_shiftLeft, Nat.testBit_shiftRight, ha₁, ha₂, he₁, he₂,
    decide_true, Bool.true_and]
  rw [Bool.or_comm (D.testBit (R+a+b)) (D.testBit (R+b))]

/-- Exact two-weight tail rule: after checking a once, one bit test checks
both new translations against all earlier subset-sum differences. -/
theorem two_weight_tail_nodup_iff {s : List ℕ} {D R : ℕ}
    (rep : centeredDiffRep s R D) (bound : ∀ x ∈ s, x ≤ R) (old : s.Nodup)
    (a b : ℕ) (leR : a ≤ R) :
    ((s ++ s.map (· + a)) ++ (s ++ s.map (· + a)).map (· + b)).Nodup ↔
      D.testBit (R+a) = false ∧ (forbiddenTailMask D R a).testBit b = false := by
  have step := addCenteredDiffMask_rep rep bound a
  have first := centeredDiff_snoc_nodup_iff rep old a
  constructor
  · intro all
    have one := all.of_append_left
    have second := (centeredDiff_snoc_nodup_iff step one b).mp all
    rw [forbiddenTailMask_testBit leR b] at second
    exact ⟨first.mp one, second⟩
  · rintro ⟨h₁,h₂⟩
    have one := first.mpr h₁
    rw [← forbiddenTailMask_testBit leR b] at h₂
    exact (centeredDiff_snoc_nodup_iff step one b).mpr h₂

def intervalMask (lo len : ℕ) : ℕ := (2^len - 1) <<< lo

theorem intervalMask_testBit (lo len b : ℕ) :
    (intervalMask lo len).testBit b = true ↔ lo ≤ b ∧ b < lo+len := by
  simp only [intervalMask, Nat.testBit_shiftLeft, Bool.and_eq_true, decide_eq_true_eq,
    Nat.testBit_two_pow_sub_one]
  omega

/-- A single mask-containment equality is exactly coverage of all
candidates in an interval, including the empty interval. -/
theorem interval_masked_iff (D lo len : ℕ) :
    ((intervalMask lo len) &&& D) = intervalMask lo len ↔
      ∀ b, lo ≤ b → b < lo+len → D.testBit b = true := by
  constructor
  · intro h b h₁ h₂
    have he := congrArg (fun n : ℕ => n.testBit b) h
    have mask := (intervalMask_testBit lo len b).mpr ⟨h₁,h₂⟩
    simpa only [Nat.testBit_land, mask, Bool.true_and] using he
  · intro covers
    apply Nat.eq_of_testBit_eq
    intro b
    rw [Nat.testBit_land]
    cases h : (intervalMask lo len).testBit b with
    | false => rfl
    | true =>
      obtain ⟨h₁,h₂⟩ := (intervalMask_testBit lo len b).mp h
      simpa only [Bool.true_and] using covers b h₁ h₂

/-- Full interval exclusion for the second of the last two weights.
This certificate has two fixed bit operations plus one interval equality;
it need not emit a collision witness for each b. -/
theorem two_weight_interval_excluded_iff {s : List ℕ} {D R : ℕ}
    (rep : centeredDiffRep s R D) (bound : ∀ x ∈ s, x ≤ R) (old : s.Nodup)
    (a lo len : ℕ) (leR : a ≤ R) :
    (∀ b, lo ≤ b → b < lo+len →
      ¬ ((s ++ s.map (· + a)) ++ (s ++ s.map (· + a)).map (· + b)).Nodup) ↔
    (D.testBit (R+a) = true ∨
      (intervalMask lo len &&& forbiddenTailMask D R a) = intervalMask lo len) := by
  simp only [two_weight_tail_nodup_iff rep bound old a _ leR, interval_masked_iff]
  constructor
  · intro excludes
    cases h : D.testBit (R+a) with
    | true => exact Or.inl rfl
    | false =>
      right
      intro b h₁ h₂
      have ne := excludes b h₁ h₂
      cases f : (forbiddenTailMask D R a).testBit b with
      | true => rfl
      | false => exact (ne ⟨h,f⟩).elim
  · intro h b h₁ h₂ good
    rcases h with hit | cover
    · rw [hit] at good
      exact Bool.noConfusion good.1
    · have hb := cover b h₁ h₂
      rw [hb] at good
      exact Bool.noConfusion good.2

#print axioms addCenteredDiffMask_rep
#print axioms centeredDiff_snoc_nodup_iff
#print axioms two_weight_tail_nodup_iff
#print axioms interval_masked_iff
#print axioms two_weight_interval_excluded_iff

end NineSeparatedSubsetSums
