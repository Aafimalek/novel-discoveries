/- Fixed-context feasibility, independent of gate counts. -/
namespace FixedOneNot

def Upward (r : α → α → Prop) (H : α → Prop) : Prop :=
  ∀ a b, r a b → H a → H b

theorem upward_separator_iff {α : Type} (r : α → α → Prop)
    (hrefl : ∀ a, r a a) (htrans : ∀ {a b c}, r a b → r b c → r a c)
    (P N : α → Prop) :
    (∃ H : α → Prop, Upward r H ∧ (∀ a, P a → H a) ∧ (∀ b, N b → ¬ H b)) ↔
    ∀ a b, P a → N b → ¬ r a b := by
  constructor
  · rintro ⟨H, hup, hp, hn⟩ a b ha hb hab
    exact hn b hb (hup a b hab (hp a ha))
  · intro h
    let H : α → Prop := fun b => ∃ a, P a ∧ r a b
    refine ⟨H, ?_, ?_, ?_⟩
    · intro a b hab ha
      rcases ha with ⟨p, hp, hpa⟩
      exact ⟨p, hp, htrans hpa hab⟩
    · intro a ha
      exact ⟨a, ha, hrefl a⟩
    · rintro b hb ⟨a, ha, hab⟩
      exact h a b ha hb hab

theorem fixed_context_iff {α : Type} (r : α → α → Prop)
    (hrefl : ∀ a, r a a) (htrans : ∀ {a b c}, r a b → r b c → r a c)
    (F0 F1 f : α → Prop)
    (hlower : ∀ x, F0 x → f x) (hupper : ∀ x, f x → F1 x) :
    (∃ H : α → Prop, Upward r H ∧
      ∀ x, ((¬ H x ∧ F1 x) ∨ (H x ∧ F0 x)) ↔ f x) ↔
    ∀ a b, (¬ f a ∧ F1 a) → (f b ∧ ¬ F0 b) → ¬ r a b := by
  classical
  rw [← upward_separator_iff r hrefl htrans
    (fun a => ¬ f a ∧ F1 a) (fun b => f b ∧ ¬ F0 b)]
  constructor
  · rintro ⟨H, hup, hfit⟩
    refine ⟨H, hup, ?_, ?_⟩
    · intro a ha
      apply Classical.byContradiction
      intro hna
      exact ha.1 ((hfit a).mp (Or.inl ⟨hna, ha.2⟩))
    · intro b hb hH
      rcases (hfit b).mpr hb.1 with (h0 | h1)
      · exact h0.1 hH
      · exact hb.2 h1.2
  · rintro ⟨H, hup, hp, hn⟩
    refine ⟨H, hup, ?_⟩
    intro x
    constructor
    · rintro (h0 | h1)
      · exact Classical.byContradiction (fun hnf => h0.1 (hp x ⟨hnf, h0.2⟩))
      · exact hlower x h1.2
    · intro hf
      by_cases hH : H x
      · exact Or.inr ⟨hH, Classical.byContradiction (fun hnf0 => hn x ⟨hf, hnf0⟩ hH)⟩
      · exact Or.inl ⟨hH, hupper x hf⟩

#print axioms upward_separator_iff
#print axioms fixed_context_iff
end FixedOneNot
