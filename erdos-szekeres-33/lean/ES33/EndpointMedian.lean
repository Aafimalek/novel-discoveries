import ES33.EndpointPacket

namespace ES33

theorem packet_even_iff {a b c d : Bool} (h : EndpointPacket a b c d) :
    oddFour a b c d = false ↔ a = b ∧ c = d := by
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp_all [EndpointPacket, oddFour]

theorem packet_middle_split {a b c d : Bool} (h : EndpointPacket a b c d)
    (hm : b ≠ c) : a = b ∧ d = c := by
  cases a <;> cases b <;> cases c <;> cases d <;> simp_all [EndpointPacket]

theorem packet_right_of_split {a b c d : Bool} (h : EndpointPacket a b c d)
    (hm : a ≠ c) : d = c := by
  cases a <;> cases b <;> cases c <;> cases d <;> simp_all [EndpointPacket]

/-- An even signotope interval admits a median-based coloring of all its triples. -/
theorem median_of_even_interval {n : ℕ}
    (χ : Fin n → Fin n → Fin n → Bool) (hχ : SignotopeConstraints n χ)
    {L R : Fin n}
    (he : ∀ a b c d, L ≤ a → a < b → b < c → c < d → d ≤ R →
      oddFour (χ a b c) (χ a b d) (χ a c d) (χ b c d) = false) :
    ∀ a b c, L ≤ a → a < b → b < c → c ≤ R →
      χ a b c = χ L b R := by
  have adj := fun a b c d (hL : L ≤ a) (ha : a < b) (hb : b < c) (hc : c < d)
      (hR : d ≤ R) => (packet_even_iff ((endpointPacket_iff _ _ _ _).mpr
        (hχ a b c d ha hb hc))).mp (he a b c d hL ha hb hc hR)
  intro a b c hL hab hbc hR
  calc
    χ a b c = χ L b c := by
      rcases hL.eq_or_lt with rfl | h
      · rfl
      · exact (adj L a b c le_rfl h hab hbc hR).2.symm
    _ = χ L b R := by
      rcases hR.eq_or_lt with rfl | h
      · rfl
      · exact (adj L b c R le_rfl (hL.trans_lt hab) hbc h le_rfl).1

/-- If two groups of interior vertices, with shared endpoints, each have
monochromatic triples of their respective color, the middle vertex
determines every triple's orientation. -/
theorem median_of_two_monochromatic_groups {n : ℕ}
    (χ : Fin n → Fin n → Fin n → Bool) (hχ : SignotopeConstraints n χ)
    {L R : Fin n}
    (hm : ∀ a b c, L ≤ a → a < b → b < c → c ≤ R →
      (a = L ∨ χ L a R = χ L b R) →
      (c = R ∨ χ L c R = χ L b R) → χ a b c = χ L b R) :
    ∀ a b c, L ≤ a → a < b → b < c → c ≤ R →
      χ a b c = χ L b R := by
  have mk := fun a b c d (ha : a < b) (hb : b < c) (hc : c < d) =>
    (endpointPacket_iff _ _ _ _).mpr (hχ a b c d ha hb hc)
  have endpoint (x y : Fin n) (hL : L < x) (hxy : x < y) (hR : y < R) :
      χ L x y = χ L x R ∧ χ x y R = χ L y R := by
    by_cases h : χ L x R = χ L y R
    · exact ⟨hm L x y le_rfl hL hxy hR.le (Or.inl rfl) (Or.inr h.symm),
        hm x y R hL.le hxy hR le_rfl (Or.inr h) (Or.inl rfl)⟩
    · exact packet_middle_split (mk L x y R hL hxy hR) h
  intro a b c hL hab hbc hR
  rcases hL.eq_or_lt with rfl | hL
  · rcases hR.eq_or_lt with rfl | hR
    · rfl
    · exact (endpoint b c hab hbc hR).1
  rcases hR.eq_or_lt with rfl | hR
  · exact (endpoint a b hL hab hbc).2
  by_cases eab : χ L a R = χ L b R
  · by_cases ebc : χ L b R = χ L c R
    · exact hm a b c hL.le hab hbc hR.le (Or.inr eab) (Or.inr ebc.symm)
    · have eb := (endpoint a b hL hab (hbc.trans hR)).2
      have ec := (endpoint a c hL (hab.trans hbc) hR).2
      have hne : χ a b R ≠ χ a c R := by simpa only [eb, ec] using ebc
      exact (packet_middle_split (mk a b c R hab hbc hR) hne).1.trans eb
  · have ea := (endpoint a b hL hab (hbc.trans hR)).1
    have eb := (endpoint b c (hL.trans hab) hbc hR).1
    have hne : χ L a b ≠ χ L b c := by simpa only [ea, eb] using eab
    exact (packet_right_of_split (mk L a b c hL hab hbc) hne).trans eb

theorem even_quad_of_median {n : ℕ} (χ : Fin n → Fin n → Fin n → Bool)
    {L R a b c d : Fin n} (hL : L ≤ a) (hab : a < b) (hbc : b < c)
    (hcd : c < d) (hR : d ≤ R)
    (hm : ∀ a b c, L ≤ a → a < b → b < c → c ≤ R →
      χ a b c = χ L b R) :
    oddFour (χ a b c) (χ a b d) (χ a c d) (χ b c d) = false := by
  rw [hm a b c hL hab hbc (hcd.le.trans hR), hm a b d hL hab (hbc.trans hcd) hR,
    hm a c d hL (hab.trans hbc) hcd hR, hm b c d (hL.trans hab.le) hbc hcd hR]
  cases χ L b R <;> cases χ L c R <;> decide

/-- For a fixed ordered signotope, the abstract parity test on an
interval is exactly the homogeneous cup/cap condition for the groups
determined by `χ L x R`. Apply to a chosen subset by reindexing. -/
theorem even_interval_iff_two_monochromatic_groups {n : ℕ}
    (χ : Fin n → Fin n → Fin n → Bool) (hχ : SignotopeConstraints n χ)
    (L R : Fin n) :
    (∀ a b c d, L ≤ a → a < b → b < c → c < d → d ≤ R →
      oddFour (χ a b c) (χ a b d) (χ a c d) (χ b c d) = false) ↔
    (∀ a b c, L ≤ a → a < b → b < c → c ≤ R →
      (a = L ∨ χ L a R = χ L b R) →
      (c = R ∨ χ L c R = χ L b R) → χ a b c = χ L b R) := by
  constructor
  · intro he a b c hL hab hbc hR _ _
    exact median_of_even_interval χ hχ he a b c hL hab hbc hR
  · intro hm a b c d hL hab hbc hcd hR
    exact even_quad_of_median χ hL hab hbc hcd hR (median_of_two_monochromatic_groups χ hχ hm)

#print axioms even_interval_iff_two_monochromatic_groups
#print axioms median_of_even_interval
#print axioms median_of_two_monochromatic_groups
#print axioms even_quad_of_median

end ES33
