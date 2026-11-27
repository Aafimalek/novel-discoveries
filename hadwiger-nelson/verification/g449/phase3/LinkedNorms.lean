import AllPublishedEdges
import AllNormsScan

namespace G449OrbitArithmetic

theorem normBare_congr (pow : Nat → V) (v w : V)
    (h : ∀ i < 12, v i = w i) (r : Nat) :
    normBare pow v r = normBare pow w r := by
  unfold normBare
  have H : (fun i : Fin 12 =>
      (List.ofFn (fun j : Fin 12 => v i.val * v j.val * pow (i.val+(42-j.val)) r)).sum) =
    (fun i : Fin 12 =>
      (List.ofFn (fun j : Fin 12 => w i.val * w j.val * pow (i.val+(42-j.val)) r)).sum) := by
    funext i
    have E : (fun j : Fin 12 => v i.val * v j.val * pow (i.val+(42-j.val)) r) =
        (fun j : Fin 12 => w i.val * w j.val * pow (i.val+(42-j.val)) r) := by
      funext j
      rw [h i.val i.isLt, h j.val j.isLt]
    rw [E]
  rw [H]

theorem normBare_neg (pow : Nat → V) (v : V) (r : Nat) :
    normBare pow (fun j => -v j) r = normBare pow v r := by
  simp only [normBare, Int.neg_mul_neg]

def rawDifference (e : Edge) : V := fun i =>
  (vertices e.a).coeffs.getD i 0 - (vertices e.b).coeffs.getD i 0

/-- Exact reduced norm and proper colouring simultaneously, on the raw
endpoint differences for every entry of the full published list. -/
theorem linked_edge_arithmetic (e : Edge) (he : e ∈ allPublishedEdges) :
    (vertices e.a).colour ≠ (vertices e.b).colour ∧
    ∀ i < 12, normBare powers (rawDifference e) i = if i = 0 then 2401 else 0 := by
  have hb := List.all_eq_true.mp all_edge_links e he
  obtain ⟨ha,hb,hd,hc,hs⟩ := Edge.validBool_sound _ _ e hb
  refine ⟨hc,?_⟩
  intro i hi
  have hnum := testNorm_sound _ _ (all_norms_scan e.d hd) i hi
  cases hf : e.flip with
  | false =>
    have heq j (hj : j < 12) : rawDifference e j = dirs e.d j := by
      simpa only [rawDifference,hf,Bool.false_eq_true,↓reduceIte] using hs j hj
    rw [normBare_congr _ _ _ heq]
    exact hnum
  | true =>
    have heq j (hj : j < 12) : rawDifference e j = -dirs e.d j := by
      simpa only [rawDifference,hf,↓reduceIte] using hs j hj
    rw [normBare_congr _ _ _ heq,normBare_neg]
    exact hnum

#print axioms linked_edge_arithmetic
end G449OrbitArithmetic
