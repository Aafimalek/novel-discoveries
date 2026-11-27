import TypedCubes
import G449Formula

namespace CertifiedG449Rotation

open G449OrbitArithmetic G449FiniteCoverage

set_option maxRecDepth 32768 in
private theorem checked_edge_order :
    allPublishedEdges.all (fun e => decide (e.a ≤ e.b)) = true := by decide +kernel

theorem proper_graph_iff_numbered_edges (f : Nat → Fin 4) :
    properGraph f ↔ CertifiedG449.proper f CertifiedG449.publishedPairs := by
  constructor
  · intro g e he
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp he
    have b := Edge.validBool_sound _ _ p (List.all_eq_true.mp all_edge_links p hp)
    have ord : p.a ≤ p.b :=
      decide_eq_true_eq.mp (List.all_eq_true.mp checked_edge_order p hp)
    have adj : Adj p.a p.b := by
      unfold Adj canonicalPair publishedPairs
      rw [if_pos ord]
      exact List.mem_map.mpr ⟨p,hp,rfl⟩
    exact g p.a p.b b.1 b.2.1 adj
  · intro g a b ha hb adj
    by_cases q : a ≤ b
    · have h : (a,b) ∈ CertifiedG449.publishedPairs := by
        change (a,b) ∈ publishedPairs
        simpa only [Adj,canonicalPair,if_pos q] using adj
      exact g (a,b) h
    · have h : (b,a) ∈ CertifiedG449.publishedPairs := by
        change (b,a) ∈ publishedPairs
        simpa only [Adj,canonicalPair,if_neg q] using adj
      exact fun eq => g (b,a) h eq.symm

/-- Any model of the exact G449 base formula gives a model, after verified
normalization, of the same base formula plus one of its six numbered cubes. -/
theorem exact_base_model_hits_cube (a : Nat → Bool) (ha : CertifiedG449.sat a CertifiedG449.formula) :
    ∃ c : Nat, c < 6 ∧ ∃ f : Nat → Fin 4,
      f center = 0 ∧ allowed c (colourWord f) = true ∧
      CertifiedG449.sat (CertifiedG449.assignment f)
        (CertifiedG449.formula ++ cubeDIMACSUnits c) := by
  obtain ⟨f,hf⟩ := CertifiedG449.g449_formula_exact_semantics.mp ⟨a,ha⟩
  obtain ⟨c,r,hc,hr,p,hp,hz,ho,_,hs⟩ :=
    proper_hits_typed_cube f ((proper_graph_iff_numbered_edges f).mpr hf)
  let g := normalize f r p
  have hbase : CertifiedG449.sat (CertifiedG449.assignment g) CertifiedG449.formula :=
    CertifiedG449.baseCNF_sat_of_proper 449 CertifiedG449.publishedPairs g
      ((proper_graph_iff_numbered_edges g).mp hp)
  refine ⟨c,hc,g,hz,ho,?_⟩
  intro cl hcl
  rcases List.mem_append.mp hcl with b | u
  · exact hbase _ b
  · exact hs _ u

#print axioms proper_graph_iff_numbered_edges
#print axioms exact_base_model_hits_cube
end CertifiedG449Rotation
