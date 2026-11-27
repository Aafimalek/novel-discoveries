import ES33.FullReduction
import Mathlib.Data.Fin.Embedding

namespace ES33.Anchor

abbrev Signs (n : ℕ) := Fin n → Fin n → Fin n → Bool

/-- All sorted triples involving the first label are positive. -/
def Anchored {n : ℕ} (χ : Signs (n+1)) : Prop :=
  ∀ b c, 0 < b → b < c → χ 0 b c = true

def residual {n : ℕ} (χ : Signs (n+1)) : Signs n :=
  fun a b c => χ a.succ b.succ c.succ

/-- Values on nonsorted triples are immaterial; assign positive whenever an
argument is the anchor, otherwise use the three residual indices. -/
def extend {n : ℕ} (r : Signs n) : Signs (n+1) :=
  Fin.cases (fun _ _ => true) (fun a =>
    Fin.cases (fun _ => true) (fun b => Fin.cases true (fun c => r a b c)))

@[simp] theorem residual_extend {n : ℕ} (r : Signs n) : residual (extend r) = r := by
  funext a b c
  simp [residual,extend]

theorem extend_anchored {n : ℕ} (r : Signs n) : Anchored (extend r) := by
  intro b c _ _
  simp [extend]

/-- For a fixed color assignment, the quadruple test used by the ES encoding. -/
def EvenSet {n : ℕ} (χ : Signs n) (s : Finset (Fin n)) : Prop :=
  ∀ a ∈ s, ∀ b ∈ s, ∀ c ∈ s, ∀ d ∈ s, a < b → b < c → c < d →
    oddFour (χ a b c) (χ a b d) (χ a c d) (χ b c d) = false

/-- A cup expressed by all of its sorted triples, not just consecutive ones.
For signotopes the two descriptions coincide by chain closure. -/
def PositiveSet {n : ℕ} (χ : Signs n) (s : Finset (Fin n)) : Prop :=
  ∀ a ∈ s, ∀ b ∈ s, ∀ c ∈ s, a < b → b < c → χ a b c = true

def HasEvenSet {n : ℕ} (χ : Signs n) (k : ℕ) : Prop :=
  ∃ s : Finset (Fin n), s.card = k ∧ EvenSet χ s

def HasPositiveSet {n : ℕ} (χ : Signs n) (k : ℕ) : Prop :=
  ∃ s : Finset (Fin n), s.card = k ∧ PositiveSet χ s

def lift {n : ℕ} (s : Finset (Fin n)) : Finset (Fin (n+1)) :=
  s.map (Fin.succEmb n)

def strip {n : ℕ} (s : Finset (Fin (n+1))) : Finset (Fin n) :=
  Finset.univ.filter (fun i => i.succ ∈ s)

@[simp] theorem mem_lift {n : ℕ} (s : Finset (Fin n)) (i : Fin n) :
    i.succ ∈ lift s ↔ i ∈ s :=
  Finset.mem_map' (Fin.succEmb n)

@[simp] theorem zero_notMem_lift {n : ℕ} (s : Finset (Fin n)) : 0 ∉ lift s := by
  intro h
  obtain ⟨a,_,ha⟩ := Finset.mem_map.mp h
  exact a.succ_ne_zero ha

@[simp] theorem card_lift {n : ℕ} (s : Finset (Fin n)) : (lift s).card = s.card :=
  Finset.card_map _

@[simp] theorem mem_strip {n : ℕ} (s : Finset (Fin (n+1))) (i : Fin n) :
    i ∈ strip s ↔ i.succ ∈ s := by
  simp [strip]

theorem lift_strip {n : ℕ} (s : Finset (Fin (n+1))) :
    lift (strip s) = s.erase 0 := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp
  · simp

private theorem succ_of_mem_lift {n : ℕ} {s : Finset (Fin n)} {a : Fin (n+1)}
    (ha : a ∈ lift s) : ∃ i ∈ s, i.succ = a := Finset.mem_map.mp ha

private theorem succ_lt {n : ℕ} {a b : Fin n} : a.succ < b.succ ↔ a < b :=
  Fin.succ_lt_succ_iff

theorem even_lift {n : ℕ} (χ : Signs (n+1)) (s : Finset (Fin n)) :
    EvenSet χ (lift s) ↔ EvenSet (residual χ) s := by
  constructor
  · intro h a ha b hb c hc d hd hab hbc hcd
    exact h a.succ ((mem_lift s a).2 ha) b.succ ((mem_lift s b).2 hb)
      c.succ ((mem_lift s c).2 hc) d.succ ((mem_lift s d).2 hd)
      (succ_lt.mpr hab) (succ_lt.mpr hbc) (succ_lt.mpr hcd)
  · intro h a ha b hb c hc d hd hab hbc hcd
    obtain ⟨a,ha_small,rfl⟩ := succ_of_mem_lift ha
    obtain ⟨b,hb_small,rfl⟩ := succ_of_mem_lift hb
    obtain ⟨c,hc_small,rfl⟩ := succ_of_mem_lift hc
    obtain ⟨d,hd_small,rfl⟩ := succ_of_mem_lift hd
    exact h a ha_small b hb_small c hc_small d hd_small (succ_lt.mp hab) (succ_lt.mp hbc) (succ_lt.mp hcd)

/-- With the anchor inserted, a set passes the even-quadruple test if and
only if all triples of its residual labels are positive. This does not
require a signotope assumption. -/
theorem even_with_anchor_iff_positive {n : ℕ} (χ : Signs (n+1)) (h0 : Anchored χ)
    (s : Finset (Fin n)) :
    EvenSet χ (insert 0 (lift s)) ↔ PositiveSet (residual χ) s := by
  constructor
  · intro h a ha b hb c hc hab hbc
    have hab' : a.succ < b.succ := succ_lt.mpr hab
    have hbc' : b.succ < c.succ := succ_lt.mpr hbc
    have ha0 : 0 < a.succ := pos_iff_ne_zero.mpr a.succ_ne_zero
    have hb0 : 0 < b.succ := ha0.trans hab'
    have H := h 0 (Finset.mem_insert_self _ _) a.succ (by simp [ha])
      b.succ (by simp [hb]) c.succ (by simp [hc]) ha0 hab' hbc'
    rw [h0 _ _ ha0 hab',h0 _ _ ha0 (hab'.trans hbc'),h0 _ _ hb0 hbc'] at H
    simpa [oddFour,residual] using H
  · intro h a ha b hb c hc d hd hab hbc hcd
    have hb0 : 0 < b := (Fin.zero_le a).trans_lt hab
    have hc0 : 0 < c := hb0.trans hbc
    have hd0 : 0 < d := hc0.trans hcd
    obtain ⟨b,hb_small,rfl⟩ := succ_of_mem_lift (Finset.mem_of_mem_insert_of_ne hb hb0.ne')
    obtain ⟨c,hc_small,rfl⟩ := succ_of_mem_lift (Finset.mem_of_mem_insert_of_ne hc hc0.ne')
    obtain ⟨d,hd_small,rfl⟩ := succ_of_mem_lift (Finset.mem_of_mem_insert_of_ne hd hd0.ne')
    have hBCD : χ b.succ c.succ d.succ = true :=
      h b hb_small c hc_small d hd_small (succ_lt.mp hbc) (succ_lt.mp hcd)
    rcases eq_or_ne a 0 with rfl | ha0
    · rw [h0 _ _ hab hbc, h0 _ _ hab (hbc.trans hcd), h0 _ _ (hab.trans hbc) hcd, hBCD]
      decide
    · obtain ⟨a,ha_small,rfl⟩ := succ_of_mem_lift (Finset.mem_of_mem_insert_of_ne ha ha0)
      have hab' := succ_lt.mp hab
      have hbc' := succ_lt.mp hbc
      have hcd' := succ_lt.mp hcd
      have hABC : χ a.succ b.succ c.succ = true := h a ha_small b hb_small c hc_small hab' hbc'
      have hABD : χ a.succ b.succ d.succ = true := h a ha_small b hb_small d hd_small hab' (hbc'.trans hcd')
      have hACD : χ a.succ c.succ d.succ = true := h a ha_small c hc_small d hd_small (hab'.trans hbc') hcd'
      rw [hABC,hABD,hACD,hBCD]
      decide

/-- Exact case split for all k: either a convex-coloring set avoids the
anchor, or it consists of the anchor and a residual positive k-set. -/
theorem has_even_set_iff {n k : ℕ} (χ : Signs (n+1)) (h0 : Anchored χ) :
    HasEvenSet χ (k+1) ↔
      HasEvenSet (residual χ) (k+1) ∨ HasPositiveSet (residual χ) k := by
  constructor
  · rintro ⟨s,hs,he⟩
    by_cases hm : 0 ∈ s
    · have insertEq : insert 0 (lift (strip s)) = s := by
        rw [lift_strip,Finset.insert_erase hm]
      have c : (strip s).card = k := by
        have hc := Finset.card_erase_add_one hm
        rw [← lift_strip,card_lift,hs] at hc
        omega
      exact Or.inr ⟨strip s,c,(even_with_anchor_iff_positive χ h0 _).mp (by simpa only [insertEq] using he)⟩
    · have liftEq : lift (strip s) = s := by
        rw [lift_strip, Finset.erase_eq_of_notMem hm]
      have c : (strip s).card = k+1 := by
        rw [← card_lift,liftEq,hs]
      exact Or.inl ⟨strip s,c,(even_lift χ _).mp (by simpa only [liftEq] using he)⟩
  · rintro (⟨s,hs,he⟩ | ⟨s,hs,he⟩)
    · exact ⟨lift s, by simp [hs], (even_lift χ s).mpr he⟩
    · refine ⟨insert 0 (lift s), ?_, (even_with_anchor_iff_positive χ h0 s).mpr he⟩
      rw [Finset.card_insert_of_notMem (zero_notMem_lift s),card_lift,hs]

theorem signotope_residual_iff {n : ℕ} (χ : Signs (n+1)) (h0 : Anchored χ) :
    SignotopeConstraints (n+1) χ ↔ SignotopeConstraints n (residual χ) := by
  constructor
  · intro h a b c d hab hbc hcd
    exact h a.succ b.succ c.succ d.succ (succ_lt.mpr hab) (succ_lt.mpr hbc) (succ_lt.mpr hcd)
  · intro h a b c d hab hbc hcd
    have hb0 : 0 < b := (Fin.zero_le a).trans_lt hab
    have hc0 : 0 < c := hb0.trans hbc
    have hd0 : 0 < d := hc0.trans hcd
    obtain ⟨b,rfl⟩ := Fin.exists_succ_eq_of_ne_zero hb0.ne'
    obtain ⟨c,rfl⟩ := Fin.exists_succ_eq_of_ne_zero hc0.ne'
    obtain ⟨d,rfl⟩ := Fin.exists_succ_eq_of_ne_zero hd0.ne'
    rcases eq_or_ne a 0 with rfl | ha0
    · dsimp only
      rw [h0 _ _ hab hbc,h0 _ _ hab (hbc.trans hcd),h0 _ _ (hab.trans hbc) hcd]
      cases χ b.succ c.succ d.succ <;> decide
    · obtain ⟨a,rfl⟩ := Fin.exists_succ_eq_of_ne_zero ha0
      exact h a b c d (succ_lt.mp hab) (succ_lt.mp hbc) (succ_lt.mp hcd)

/-- A pure SAT-level equivalence, not a theorem that all signotopes are real.
The geometric normalization that licenses the anchor is a separate step. -/
theorem anchored_avoidance_iff_residual {n k : ℕ} :
    (∃ χ : Signs (n+1), Anchored χ ∧ SignotopeConstraints (n+1) χ ∧
      ¬ HasEvenSet χ (k+1)) ↔
    (∃ r : Signs n, SignotopeConstraints n r ∧
      (¬ HasEvenSet r (k+1)) ∧ (¬ HasPositiveSet r k)) := by
  constructor
  · rintro ⟨χ,h0,hχ,hA⟩
    refine ⟨residual χ,(signotope_residual_iff χ h0).mp hχ,?_,?_⟩
    · exact fun h => hA ((has_even_set_iff χ h0).mpr (Or.inl h))
    · exact fun h => hA ((has_even_set_iff χ h0).mpr (Or.inr h))
  · rintro ⟨r,hr,hN,hC⟩
    have h0 := extend_anchored r
    refine ⟨extend r,h0,(signotope_residual_iff (extend r) h0).mpr (by simpa using hr),?_⟩
    intro h
    rcases (has_even_set_iff (extend r) h0).mp h with h|h
    · exact hN (by simpa using h)
    · exact hC (by simpa using h)

/-- The existing abstract 7-avoidance clauses are exactly the absence
of a 7-set with every ordered quartet of even parity. -/
theorem avoidanceClauses_iff {n : ℕ} (χ : Signs n) :
    AvoidanceClauses n χ ↔ ¬ HasEvenSet χ 7 := by
  constructor
  · rintro h ⟨s,hs,even⟩
    obtain ⟨a,ha,b,hb,c,hc,d,hd,hab,hbc,hcd,odd⟩ := h s hs
    rw [even a ha b hb c hc d hd hab hbc hcd] at odd
    exact Bool.false_ne_true odd
  · intro h s hs
    by_contra hbad
    apply h
    refine ⟨s,hs,?_⟩
    intro a ha b hb c hc d hd hab hbc hcd
    cases hb' : oddFour (χ a b c) (χ a b d) (χ a c d) (χ b c d)
    · rfl
    · exact False.elim (hbad ⟨a,ha,b,hb,c,hc,d,hd,hab,hbc,hcd,hb'⟩)

/-- The exact abstract 33-to-32 reduction for the existing ES33 clause family. -/
theorem anchored_ES33_iff_residual :
    (∃ χ : Signs 33, Anchored χ ∧ SignotopeConstraints 33 χ ∧ AvoidanceClauses 33 χ) ↔
    (∃ r : Signs 32, SignotopeConstraints 32 r ∧ AvoidanceClauses 32 r ∧
      ¬ HasPositiveSet r 6) := by
  simpa only [avoidanceClauses_iff] using (anchored_avoidance_iff_residual (n := 32) (k := 6))

#print axioms anchored_ES33_iff_residual
#print axioms even_with_anchor_iff_positive
#print axioms has_even_set_iff
#print axioms signotope_residual_iff
#print axioms anchored_avoidance_iff_residual

end ES33.Anchor
