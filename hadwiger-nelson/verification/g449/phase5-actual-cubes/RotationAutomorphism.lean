import CentralChecks
import AllRotatedEdges

namespace CertifiedG449Rotation

open G449OrbitArithmetic

theorem row_mem_iff_pair (a b : Nat) (ha : a < 449) :
    b ∈ upperNeighbors a ↔ (a,b) ∈ publishedPairs := by
  rw [← checked_exact_pair_table]
  constructor
  · intro h
    exact List.mem_flatMap.mpr ⟨a,List.mem_range.mpr ha,List.mem_map.mpr ⟨b,h,rfl⟩⟩
  · intro h
    obtain ⟨d,_,hd⟩ := List.mem_flatMap.mp h
    obtain ⟨v,hv,hpv⟩ := List.mem_map.mp hd
    have p := Prod.mk.inj hpv
    simpa [p.1,p.2] using hv

theorem adjB_iff_Adj (a b : Nat) (ha : a < 449) (hb : b < 449) :
    adjB a b = true ↔ Adj a b := by
  unfold adjB Adj canonicalPair
  by_cases h : a ≤ b
  · rw [if_pos h,if_pos h]
    exact List.contains_iff_mem.trans (row_mem_iff_pair a b ha)
  · rw [if_neg h,if_neg h]
    exact List.contains_iff_mem.trans (row_mem_iff_pair b a hb)

theorem adjB_symm (a b : Nat) : adjB a b = adjB b a := by
  by_cases h : a = b
  · simp [h]
  by_cases q : a ≤ b
  · have t : ¬ b ≤ a := by omega
    simp [adjB,q,t]
  · have t : b ≤ a := by omega
    simp [adjB,q,t]

/-- Both lookup maps stay on the source vertex set and are mutual inverses. -/
theorem rot_inv_on_published_vertices (k : Nat) (hk : k < 449) :
    rot k < 449 ∧ inv k < 449 ∧ inv (rot k) = k ∧ rot (inv k) = k := by
  have h := List.all_eq_true.mp checked_inverse_rotation k (List.mem_range.mpr hk)
  simp only [permOK,Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq] at h
  exact ⟨h.1.1.1,h.1.1.2,h.1.2,h.2⟩

theorem map_preserves_of_edge_checks (f : Nat → Nat)
    (bound : ∀ i < 449, f i < 449)
    (ok : ∀ e ∈ allPublishedEdges, adjB (f e.a) (f e.b) = true)
    (a b : Nat) (ha : a < 449) (hb : b < 449) (h : Adj a b) :
    Adj (f a) (f b) := by
  apply (adjB_iff_Adj _ _ (bound a ha) (bound b hb)).mp
  by_cases q : a ≤ b
  · have z : (a,b) ∈ publishedPairs := by simpa only [Adj,canonicalPair,if_pos q] using h
    obtain ⟨e,he,hp⟩ := List.mem_map.mp z
    have z := Prod.mk.inj hp
    simpa only [z.1,z.2] using ok e he
  · have z : (b,a) ∈ publishedPairs := by simpa only [Adj,canonicalPair,if_neg q] using h
    obtain ⟨e,he,hp⟩ := List.mem_map.mp z
    have z := Prod.mk.inj hp
    rw [adjB_symm]
    simpa only [z.1,z.2] using ok e he

theorem forward_rotation (a b : Nat) (ha : a < 449) (hb : b < 449) (h : Adj a b) :
    Adj (rot a) (rot b) :=
  map_preserves_of_edge_checks rot
    (fun i hi => (rot_inv_on_published_vertices i hi).1)
    (fun e he => (Bool.and_eq_true_iff.mp (List.all_eq_true.mp checked_rotation_of_published_edges e he)).1)
    a b ha hb h

theorem inverse_preserves (a b : Nat) (ha : a < 449) (hb : b < 449) (h : Adj a b) :
    Adj (inv a) (inv b) :=
  map_preserves_of_edge_checks inv
    (fun i hi => (rot_inv_on_published_vertices i hi).2.1)
    (fun e he => (Bool.and_eq_true_iff.mp (List.all_eq_true.mp checked_rotation_of_published_edges e he)).2)
    a b ha hb h

/-- The actual G449 rotation preserves and reflects the complete published
undirected adjacency relation, not merely a computed subset. -/
theorem G449_rotation_automorphism (a b : Nat) (ha : a < 449) (hb : b < 449) :
    Adj (rot a) (rot b) ↔ Adj a b := by
  constructor
  · intro h
    have p := rot_inv_on_published_vertices a ha
    have q := rot_inv_on_published_vertices b hb
    have H := inverse_preserves _ _ p.1 q.1 h
    simpa only [p.2.2.1,q.2.2.1] using H
  · exact forward_rotation a b ha hb

/-- The ordered list is exactly the central-neighbour set on all 449
vertices, not just a list of seven neighbours known to be adjacent. -/
theorem G449_central_neighbors_complete (a : Nat) (ha : a < 449) :
    Adj center a ↔ a ∈ ring := by
  have h := List.all_eq_true.mp checked_neighbors a (List.mem_range.mpr ha)
  have he : adjB center a = ring.contains a := beq_iff_eq.mp h
  rw [← adjB_iff_Adj center a checked_center.1 ha,he]
  exact List.contains_iff_mem

theorem G449_central_neighbors_cycle (i : Nat) (hi : i < 7) :
    rot (ring.getD i 0) = ring.getD ((i+1)%7) 0 :=
  beq_iff_eq.mp (List.all_eq_true.mp checked_neighbor_cycle i (List.mem_range.mpr hi))

theorem G449_central_neighbors_independent (a b : Nat) (ha : a ∈ ring) (hb : b ∈ ring)
    (hne : a ≠ b) : ¬ Adj a b := by
  intro hh
  have hA : a < 449 := decide_eq_true_eq.mp (List.all_eq_true.mp checked_ring_labels.2.2 a ha)
  have hB : b < 449 := decide_eq_true_eq.mp (List.all_eq_true.mp checked_ring_labels.2.2 b hb)
  have h := List.all_eq_true.mp (List.all_eq_true.mp checked_neighbor_independence a ha) b hb
  have yes := (adjB_iff_Adj a b hA hB).mpr hh
  simp [hne,yes] at h

#print axioms rot_inv_on_published_vertices
#print axioms G449_rotation_automorphism
#print axioms G449_central_neighbors_complete
#print axioms G449_central_neighbors_cycle
#print axioms G449_central_neighbors_independent

end CertifiedG449Rotation
