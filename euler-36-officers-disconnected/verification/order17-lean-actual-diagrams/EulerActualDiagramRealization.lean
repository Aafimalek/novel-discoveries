import EulerActualSymbolRanks

namespace LatinGap
open EulerAllUsedDiagrams

def actualRowCodes (W : Coord → Word 6) : List Nat :=
  List.ofFn fun i : Coord =>
    (List.ofFn fun j : Coord => (W i j).val).foldl (fun a b => a * 10 + b) 0

private theorem indices_map {α : Type} (f : Nat → α) :
    indices.map f = List.ofFn (fun i : Coord => f i.val) := rfl

private theorem bb {α : Type} (f : Coord → α) (i : Coord) (deflt : α) :
    (List.ofFn f).getD i.val deflt = f i := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dite_eq_left i.isLt]
  rfl

theorem archive_normalize_eq_actual_codes
    (m : List (List Nat)) (p : List Nat) (V W : Coord → Word 6)
    (entries : ∀ i j : Coord, (V i j).val = value m (p.getD i.val 0) (p.getD j.val 0))
    (ranked : ∀ i j : Coord, (W i j).val = archivedRank V i j) :
    normalize m p = actualRowCodes W := by
  let entry (i j : Nat) := value m (p.getD i 0) (p.getD j 0)
  let ranks := indices.map fun j =>
    ((indices.map fun i => entry i j).filter fun v => v != 0).eraseDups
  let digit (i j : Nat) := if entry i j == 0 then 0 else
    ((ranks.getD j []).idxOf (entry i j)) + 1
  change (indices.map (fun i => (indices.map (digit i)).foldl (fun a b => a*10+b) 0)) =
    actualRowCodes W
  rw [indices_map]
  unfold actualRowCodes
  apply congrArg List.ofFn
  funext i
  rw [indices_map]
  apply congrArg (fun l : List Nat => l.foldl (fun a b => a*10+b) 0)
  apply congrArg List.ofFn
  funext j
  rw [ranked]
  have hranks : ranks.getD j.val [] = (nonzeroColumn V j).eraseDups := by
    unfold ranks
    rw [indices_map, bb, indices_map]
    unfold nonzeroColumn
    congr 2
    exact congrArg List.ofFn (funext (fun u => (entries u j).symm))
  have e : entry i.val j.val = (V i j).val := (entries i j).symm
  unfold digit archivedRank
  rw [e,hranks]
  by_cases h : V i j = 0
  · simp [h]
  · have hn : (V i j).val ≠ 0 := fun hz => h (Fin.ext hz)
    simp [h,hn]
    rfl

/-- Geometric realization of one of the published seventeen diagrams:
the four final words actually occur in a renamed linear saturated
design, not just in an abstract enumeration. -/
theorem all_used_realizes_published {D : Design 6} (hD : Linear D)
    (hS : Saturated D) (a : Word 6) (ha : a ∈ D)
    (hfreq : ∀ j, freq D (j,a j) = 2) :
    ∃ G : Design 6, Linear G ∧ Saturated G ∧ G.card = D.card ∧
      (fun _ => 0) ∈ G ∧ (∀ j, freq G (j,0) = 2) ∧
      ∃ W : Coord → Word 6,
        (∀ i, W i ∈ G ∧ W i i = 0 ∧ ∀ j ≠ i, W i j ≠ 0) ∧
        actualRowCodes W ∈ published := by
  obtain ⟨E,hE,hsE,hcE,hzE,hlE,U,_,hU,p,hp,_,hpub⟩ :=
    all_used_actual_published hD hS a ha hfreq
  let k := archivedCoordinatePerm p hp
  let F := renameDesign k (fun _ => Equiv.refl _) E
  let V (i : Coord) := renameWords k (fun _ => Equiv.refl _) (U (k i))
  have hphysical := archived_permutation_realizes_outer hE hsE hzE hlE U hU p hp
  change Linear F ∧ Saturated F ∧ F.card=E.card ∧ (fun _ => 0)∈F ∧
      (∀ j, freq F (j,0)=2) ∧ (∀ i, V i ∈ F ∧ V i i = 0 ∧ ∀ j ≠ i, V i j ≠ 0) ∧
      (∀ i j : Coord, (V i j).val = value (ofColumns (outerColumns U))
        (p.getD i.val 0) (p.getD j.val 0)) at hphysical
  obtain ⟨hF,hsF,hcF,hzF,hlF,hV,hentry⟩ := hphysical
  obtain ⟨lab,fixed,ranked⟩ :=
    geometric_rank_renaming V (fun i => (hV i).2.1) (fun i => (hV i).2.2)
  let I : Coord ≃ Coord := Equiv.refl _
  let G := renameDesign I lab F
  let W (i : Coord) := renameWords I lab (V i)
  have codes := archive_normalize_eq_actual_codes (ofColumns (outerColumns U)) p V W hentry ranked
  refine ⟨G,renameDesign_linear hF _ _,renameDesign_saturated hsF _ _,
    (renameDesign_card _ _ _).trans (hcF.trans hcE),?_,?_,W,?_,codes ▸ hpub⟩
  · refine Finset.mem_map.mpr ⟨_,hzF,?_⟩
    funext j
    exact fixed j
  · intro j
    have h := renameDesign_freq I lab F j 0
    rw [fixed j] at h
    exact h.trans (hlF j)
  · intro i
    refine ⟨Finset.mem_map.mpr ⟨_,(hV i).1,rfl⟩,?_,?_⟩
    · change lab i (V i i) = 0
      rw [(hV i).2.1,fixed i]
    · intro j ne h
      change lab j (V i j) = 0 at h
      rw [← fixed j] at h
      exact (hV i).2.2 j ne ((lab j).injective h)

#print axioms archive_normalize_eq_actual_codes
#print axioms all_used_realizes_published
end LatinGap
