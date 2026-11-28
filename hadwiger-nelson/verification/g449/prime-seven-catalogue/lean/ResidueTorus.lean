import Mod7Trace

namespace CyclotomicModSeven

def residueProper (c : F7 → F7 → Fin n) : Prop :=
  ∀ x y u v : F7, (x-u)*(y-v)=1 → c x y ≠ c u v

def basisX (i j : F7) : F7 := 3*i+5*j
def basisY (i j : F7) : F7 := 5*i+3*j

/-- In this basis the six norm-one offsets form the triangular 7 by 7 torus. -/
def torusOffsets (i j : F7) : Prop :=
  (i=1 ∧ j=0) ∨ (i=6 ∧ j=0) ∨ (i=0 ∧ j=1) ∨
  (i=0 ∧ j=6) ∨ (i=1 ∧ j=1) ∨ (i=6 ∧ j=6)

theorem basis_adjacency : ∀ i j u v : F7,
    (basisX i j-basisX u v)*(basisY i j-basisY u v)=1 ↔
      torusOffsets (u-i) (v-j) := by
  unfold torusOffsets
  decide +kernel

theorem basis_inverse_valid : ∀ i j x y : F7,
    basisX (2*x+6*y) (6*x+2*y)=x ∧ basisY (2*x+6*y) (6*x+2*y)=y ∧
      2*basisX i j+6*basisY i j=i ∧ 6*basisX i j+2*basisY i j=j := by
  decide +kernel

private theorem positive_step_norms : ∀ i j : F7,
    (basisX i j-basisX (i+1) j)*(basisY i j-basisY (i+1) j)=1 ∧
    (basisX i j-basisX i (j+1))*(basisY i j-basisY i (j+1))=1 ∧
    (basisX i j-basisX (i+1) (j+1))*(basisY i j-basisY (i+1) (j+1))=1 := by
  decide +kernel

private theorem same_missing_colour : ∀ a b c d : Fin 3,
    a ≠ b → a ≠ c → d ≠ b → d ≠ c → b ≠ c → a=d := by
  decide +kernel

private theorem plus_twice : ∀ i : F7, i+1+1=i+2 := by decide +kernel
private theorem plus_two_from_next : ∀ i : F7, i+1+2=i+3 := by decide +kernel
private theorem plus_one_from_second : ∀ i : F7, i+2+1=i+3 := by decide +kernel

theorem triangular_torus_not_three (f : F7 → F7 → Fin 3)
    (hx : ∀ i j, f i j ≠ f (i+1) j)
    (hy : ∀ i j, f i j ≠ f i (j+1))
    (hd : ∀ i j, f i j ≠ f (i+1) (j+1)) : False := by
  have opp (i j : F7) : f (i+1) j = f i (j+1) :=
    same_missing_colour _ _ _ _ (fun h => hx i j h.symm)
      (hy (i+1) j) (fun h => hy i j h.symm) (hx i (j+1)) (hd i j)
  let g : F7 → Fin 3 := fun i => f i 0
  have step (i : F7) : g i ≠ g (i+1) := hx i 0
  have skip (i : F7) : g i ≠ g (i+2) := by
    have h := hd i 0
    have hb := (opp (i+1) 0).symm
    rw [plus_twice] at hb
    exact fun eq => h (eq.trans hb.symm)
  have period (i : F7) : g i = g (i+3) := by
    have u : g (i+1) ≠ g (i+3) := by
      have e := skip (i+1)
      rwa [plus_two_from_next] at e
    have v : g (i+2) ≠ g (i+3) := by
      have e := step (i+2)
      rwa [plus_one_from_second] at e
    have w := step (i+1)
    rw [plus_twice] at w
    exact same_missing_colour _ _ _ _ (step i) (skip i)
      (fun eq => u eq.symm) (fun eq => v eq.symm) w
  have p0 : g 0=g 3 := period 0
  have p3 : g 3=g 6 := period 3
  have p6 : g 6=g 2 := period 6
  have p2 : g 2=g 5 := period 2
  have p5 : g 5=g 1 := period 5
  exact step 0 (p0.trans (p3.trans (p6.trans (p2.trans p5))))

/-- Sharpness of four on the finite residue graph, not a claim on the real plane. -/
theorem residue_norm_graph_not_three (c : F7 → F7 → Fin 3) (hc : residueProper c) : False := by
  let f := fun i j => c (basisX i j) (basisY i j)
  apply triangular_torus_not_three f
  · intro i j
    exact hc _ _ _ _ (positive_step_norms i j).1
  · intro i j
    exact hc _ _ _ _ (positive_step_norms i j).2.1
  · intro i j
    exact hc _ _ _ _ (positive_step_norms i j).2.2

#print axioms basis_adjacency
#print axioms basis_inverse_valid
#print axioms residue_norm_graph_not_three

end CyclotomicModSeven
