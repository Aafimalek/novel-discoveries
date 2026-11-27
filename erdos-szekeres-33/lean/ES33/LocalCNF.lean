import ES33.FullReduction

namespace ES33

abbrev Packet := Bool × Bool × Bool × Bool

/-- Exactly the orientation packets with at most one change. -/
def packetAllowed (r : Packet) : Prop :=
  let (a,b,c,d) := r
  (a ≤ b ∧ b ≤ c ∧ c ≤ d) ∨ (d ≤ c ∧ c ≤ b ∧ b ≤ a)

/-- The eight ternary clauses produced by the exact local minimizer.
Slots a,b,c,d are the sorted triple signs; q is the nonconvexity bit. -/
def CompactPacket (a b c d q : Bool) : Prop :=
  (a ∨ d ∨ q = false) ∧
  (c ∨ d = false ∨ q) ∧
  (b ∨ c = false ∨ q = false) ∧
  (a ∨ b = false ∨ q) ∧
  (a = false ∨ b ∨ q) ∧
  (b = false ∨ c ∨ q = false) ∧
  (c = false ∨ d ∨ q) ∧
  (a = false ∨ d = false ∨ q = false)

/-- The compact eight-clause encoding is exactly equivalent to the
geometric signotope condition and parity indicator. -/
theorem compact_packet_iff (a b c d q : Bool) :
    CompactPacket a b c d q ↔ packetAllowed (a,b,c,d) ∧ q = oddFour a b c d := by
  cases a <;> cases b <;> cases c <;> cases d <;> cases q <;>
    simp [CompactPacket,packetAllowed,oddFour]

/-- The eight local ternary clauses for every ordered quadruple and
one positive disjunction of its thirty-five auxiliary variables for
every seven-set. -/
def CompactClauseFamily (n : ℕ)
    (χ : Fin n → Fin n → Fin n → Bool)
    (q : Fin n → Fin n → Fin n → Fin n → Bool) : Prop :=
  (∀ a b c d : Fin n, a < b → b < c → c < d →
    CompactPacket (χ a b c) (χ a b d) (χ a c d) (χ b c d) (q a b c d)) ∧
  (∀ t : Finset (Fin n), t.card = 7 →
    ∃ a ∈ t, ∃ b ∈ t, ∃ c ∈ t, ∃ d ∈ t, a < b ∧ b < c ∧ c < d ∧ q a b c d = true)

theorem compact_clause_family_iff (n : ℕ) (χ : Fin n → Fin n → Fin n → Bool) :
    (∃ q : Fin n → Fin n → Fin n → Fin n → Bool, CompactClauseFamily n χ q) ↔
      SignotopeConstraints n χ ∧ AvoidanceClauses n χ := by
  constructor
  · rintro ⟨q,hloc,hsets⟩
    constructor
    · intro a b c d hab hbc hcd
      exact (compact_packet_iff _ _ _ _ _).mp (hloc a b c d hab hbc hcd) |>.1
    · intro t ht
      obtain ⟨a,ha,b,hb,c,hc,d,hd,hab,hbc,hcd,hq⟩ := hsets t ht
      have aux := (compact_packet_iff _ _ _ _ _).mp (hloc a b c d hab hbc hcd) |>.2
      exact ⟨a,ha,b,hb,c,hc,d,hd,hab,hbc,hcd,aux ▸ hq⟩
  · rintro ⟨hs,hav⟩
    refine ⟨fun a b c d => oddFour (χ a b c) (χ a b d) (χ a c d) (χ b c d), ?_, hav⟩
    intro a b c d hab hbc hcd
    exact (compact_packet_iff _ _ _ _ _).mpr ⟨hs a b c d hab hbc hcd,rfl⟩

/-- The exact point theorem follows if an independent proof excludes all
assignments to the compact clause family. This is not that exclusion. -/
theorem es33_of_compact_clause_unsat
    (unsat : ¬ ∃ (χ : Fin 33 → Fin 33 → Fin 33 → Bool)
      (q : Fin 33 → Fin 33 → Fin 33 → Fin 33 → Bool), CompactClauseFamily 33 χ q)
    (p : Fin 33 ↪ Plane) (gp : GeneralPositionAll p) :
    ∃ s : Finset Plane, s ⊆ Finset.univ.map p ∧ s.card = 7 ∧ ConvexPosition s := by
  apply es33_of_clause_unsat _ p gp
  rintro ⟨χ,hχ⟩
  obtain ⟨q,hq⟩ := (compact_clause_family_iff 33 χ).mpr hχ
  exact unsat ⟨χ,q,hq⟩

/-- Exact dimensions of the compact relaxation: one variable per
triple or quadruple, eight clauses per quadruple and one per 7-set. -/
theorem compact_dimensions :
    Nat.choose 33 3 + Nat.choose 33 4 = 46376 ∧
    8 * Nat.choose 33 4 + Nat.choose 33 7 = 4599408 ∧
    Nat.choose 7 4 = 35 := by decide +kernel

#print axioms compact_packet_iff
#print axioms compact_clause_family_iff
#print axioms es33_of_compact_clause_unsat
#print axioms compact_dimensions

end ES33
