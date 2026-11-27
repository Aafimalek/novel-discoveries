import PEqualNP.Defs.MetaComplexityLgpMono
import Mathlib.Tactic

namespace SharedOutputs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

/-- Use the same DAG once, adding one AND gate for its two outputs. -/
def meet (c d : Circuit) (n : ℕ) : Circuit :=
  ⟨c.gates ++ [⟨GateOp.and, [c.output, d.output]⟩], n + c.gates.length⟩

theorem wires_length (c : Circuit) (x : List Bool) :
    (c.wires x).length = x.length + c.gates.length := by
  obtain ⟨gs,i⟩ := c
  unfold Circuit.wires
  change (gs.foldl _ x).length = x.length + gs.length
  induction gs generalizing x with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

theorem eval_meet (c d : Circuit) (n : ℕ) (x : List Bool)
    (len : x.length = n) (hg : c.gates = d.gates) :
    (meet c d n).eval x = (c.eval x && d.eval x) := by
  have hw : c.wires x = d.wires x := by simp [Circuit.wires, hg]
  have hl : (c.wires x).length = n + c.gates.length := by rw [wires_length, len]
  unfold Circuit.eval
  change ((c.gates ++ [(⟨GateOp.and,[c.output,d.output]⟩ : Gate)]).foldl _ x).getD
    (n + c.gates.length) false = _
  rw [List.foldl_append]
  change (c.wires x ++ [GateOp.and.eval ([c.output,d.output].map
    (fun i => (c.wires x).getD i false))]).getD (n + c.gates.length) false = _
  rw [← hl]
  simp [List.getD_eq_getElem?_getD, GateOp.eval, hw]

theorem size_meet (c d : Circuit) (n : ℕ) : (meet c d n).size = c.size + 1 := by
  simp [meet, Circuit.size]

theorem monotone_meet (c d : Circuit) (n : ℕ) (h : Monotone2 c) :
    Monotone2 (meet c d n) := by
  intro g hg
  change g ∈ c.gates ++ [(⟨GateOp.and, [c.output, d.output]⟩ : Gate)] at hg
  rcases List.mem_append.mp hg with old | new
  · exact h g old
  · have e := List.mem_singleton.mp new
    subst g
    simp

/-- Two shared-DAG outputs accepting all positive examples, with no common
accepted negative example, yield a separator with one extra gate. -/
theorem separator_meet (c d : Circuit) (n : ℕ) (P N : List Bool → Prop)
    (same : c.gates = d.gates) (mc : Monotone2 c)
    (lengths : ∀ xs, P xs ∨ N xs → xs.length = n)
    (pos : ∀ xs, P xs → c.eval xs = true ∧ d.eval xs = true)
    (neg : ∀ xs, N xs → ¬ (c.eval xs = true ∧ d.eval xs = true)) :
    ∃ s : Circuit, s.size = c.size + 1 ∧ Monotone2 s ∧
      (∀ xs, P xs → s.eval xs = true) ∧ (∀ xs, N xs → s.eval xs = false) := by
  refine ⟨meet c d n, size_meet c d n, monotone_meet c d n mc, ?_, ?_⟩
  · intro xs hx
    rw [eval_meet c d n xs (lengths xs (Or.inl hx)) same, (pos xs hx).1, (pos xs hx).2]
    rfl
  · intro xs hx
    rw [eval_meet c d n xs (lengths xs (Or.inr hx)) same]
    have hn := neg xs hx
    cases e₁ : c.eval xs <;> cases e₂ : d.eval xs <;> simp_all

#print axioms eval_meet
#print axioms separator_meet

end SharedOutputs
