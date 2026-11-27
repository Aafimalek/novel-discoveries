import Init

namespace CertifiedG449

def var (v : Nat) (c : Fin 4) : Nat := 4*v+c.val+1

def vertexClause (v : Nat) : List Int :=
  [(var v 0 : Int),(var v 1 : Int),(var v 2 : Int),(var v 3 : Int)]

def edgeClause (e : Nat × Nat) (c : Fin 4) : List Int :=
  [-(var e.1 c : Int),-(var e.2 c : Int)]

def baseCNF (n : Nat) (edges : List (Nat × Nat)) : List (List Int) :=
  (List.range n).map vertexClause ++
    edges.flatMap (fun e => [edgeClause e 0,edgeClause e 1,edgeClause e 2,edgeClause e 3])

def litSat (a : Nat → Bool) (l : Int) : Prop :=
  if 0 < l then a l.toNat = true else a (-l).toNat = false

def sat (a : Nat → Bool) (f : List (List Int)) : Prop :=
  ∀ c ∈ f, ∃ l ∈ c, litSat a l

def proper (colour : Nat → Fin 4) (edges : List (Nat × Nat)) : Prop :=
  ∀ e ∈ edges, colour e.1 ≠ colour e.2

def assignment (colour : Nat → Fin 4) (n : Nat) : Bool :=
  decide ((colour ((n-1)/4)).val = (n-1)%4)

theorem assignment_exact (colour : Nat → Fin 4) (v : Nat) (c : Fin 4) :
    assignment colour (var v c) = true ↔ colour v = c := by
  unfold assignment var
  have hd : (4*v+c.val+1-1)/4 = v := by omega
  have hm : (4*v+c.val+1-1)%4 = c.val := by omega
  rw [hd,hm,decide_eq_true_eq]
  exact Fin.val_inj

theorem litSat_pos_var (a : Nat → Bool) (v : Nat) (c : Fin 4) :
    litSat a (var v c : Int) ↔ a (var v c) = true := by
  have h : (0 : Int) < (var v c : Int) := by unfold var; omega
  unfold litSat
  rw [if_pos h]
  rfl

theorem litSat_neg_var (a : Nat → Bool) (v : Nat) (c : Fin 4) :
    litSat a (-(var v c : Int)) ↔ a (var v c) = false := by
  have h : ¬ (0 : Int) < -(var v c : Int) := by omega
  unfold litSat
  rw [if_neg h, Int.neg_neg]
  rfl

theorem vertex_contains (v : Nat) (c : Fin 4) : (var v c : Int) ∈ vertexClause v := by
  have h : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 := by omega
  rcases h with h | h | h | h <;> subst c <;> simp [vertexClause]

/-- The numeric DIMACS formulas' clause layout is sound: a proper four-colouring
would satisfy every vertex clause and every edge exclusion clause. -/
theorem baseCNF_sat_of_proper (n : Nat) (edges : List (Nat × Nat))
    (colour : Nat → Fin 4) (h : proper colour edges) :
    sat (assignment colour) (baseCNF n edges) := by
  intro cl hcl
  rw [baseCNF,List.mem_append] at hcl
  rcases hcl with hm | hm
  · obtain ⟨v,_,rfl⟩ := List.mem_map.mp hm
    refine ⟨(var v (colour v) : Int),vertex_contains _ _,?_⟩
    exact (litSat_pos_var _ _ _).mpr ((assignment_exact _ _ _).mpr rfl)
  · obtain ⟨e,he,hc⟩ := List.mem_flatMap.mp hm
    have hshape : ∃ q : Fin 4, cl = edgeClause e q := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact ⟨0,rfl⟩
      · exact ⟨1,rfl⟩
      · exact ⟨2,rfl⟩
      · exact ⟨3,rfl⟩
    obtain ⟨q,rfl⟩ := hshape
    have hf v (hn : colour v ≠ q) : assignment colour (var v q) = false := by
      have hnot : ¬ assignment colour (var v q) = true := fun e => hn ((assignment_exact _ _ _).mp e)
      cases e : assignment colour (var v q) with
      | false => rfl
      | true => exact (hnot e).elim
    by_cases h1 : colour e.1 = q
    · have h2 : colour e.2 ≠ q := by intro h'; exact h e he (h1.trans h'.symm)
      exact ⟨-(var e.2 q : Int),by simp [edgeClause],(litSat_neg_var _ _ _).mpr (hf _ h2)⟩
    · exact ⟨-(var e.1 q : Int),by simp [edgeClause],(litSat_neg_var _ _ _).mpr (hf _ h1)⟩

/-- This is the logical implication a checked UNSAT proof needs. -/
theorem no_proper_four_of_base_unsat (n : Nat) (edges : List (Nat × Nat))
    (unsat : ∀ a, ¬ sat a (baseCNF n edges)) :
    ¬ ∃ colour, proper colour edges := by
  rintro ⟨c,hc⟩
  exact unsat _ (baseCNF_sat_of_proper n edges c hc)

#print axioms assignment_exact
#print axioms baseCNF_sat_of_proper
#print axioms no_proper_four_of_base_unsat

end CertifiedG449
