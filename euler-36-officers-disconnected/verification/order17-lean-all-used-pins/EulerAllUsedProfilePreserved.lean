import EulerActualDiagramRealization

namespace LatinGap
open EulerAllUsedDiagrams

private theorem column_permutation_withProfile (a : Word 6) (W : Coord → Word 6)
    (only : ∀ i j : Coord, j ≠ i → W i j ≠ a j) (j : Coord) :
    ∃ p : Equiv.Perm (Fin 6), p (a j) = 0 ∧
      outerColumn (fun i k => p (W i k)) j ∈ outerPatterns := by
  let A := W (outerRows j 0) j
  let B := W (outerRows j 1) j
  let C := W (outerRows j 2) j
  obtain ⟨p,h0,h1,h2,h3⟩ :=
    first_occurrence_pattern (a j) A B C
      (only _ j (outerRows_ne j 0).symm)
      (only _ j (outerRows_ne j 1).symm)
      (only _ j (outerRows_ne j 2).symm)
  refine ⟨p,h0,?_⟩
  have exactColumn : outerColumn (fun i k => p (W i k)) j =
      [(p A).val,(p B).val,(p C).val] := by rfl
  rw [exactColumn,h1,h2,h3]
  by_cases e : B = A
  · by_cases h : C = A
    · simp [outerPatterns,e,h]
    · have h' : C ≠ B := fun he => h (he.trans e)
      simp [outerPatterns,e,h,h']
  · by_cases h : C = A
    · simp [outerPatterns,e,h]
    · by_cases h' : C = B <;> simp [outerPatterns,e,h,h']

/-- The actual four outer words can be normalized simultaneously in each
column, keeping the prescribed central word at zero and preserving all
geometric hypotheses. Any two outer rows agree in at most one column. -/
private theorem normalize_all_used_outer_patterns_withProfile {D : Design 6} (hD : Linear D)
    (hS : Saturated D) (a : Word 6) (ha : a ∈ D)
    (hfreq : ∀ j, freq D (j,a j) = 2)
    (initial : ∀ (g : Coord) (b : Fin 6), b ≠ a g → freq D (g,b) = 3) :
    ∃ E : Design 6, Linear E ∧ Saturated E ∧ E.card = D.card ∧
      (fun _ => 0) ∈ E ∧ (∀ j, freq E (j,0) = 2) ∧
      (∀ (j : Coord) (b : Fin 6), b ≠ 0 → freq E (j,b) = 3) ∧
      ∃ U : Coord → Word 6, Function.Injective U ∧
        (∀ i, U i ∈ E ∧ U i i = 0 ∧ ∀ j ≠ i, U i j ≠ 0) ∧
        (∀ j, outerColumn U j ∈ outerPatterns) ∧
        (∀ i j u v : Coord, i ≠ j → u ≠ v → U i u = U j u → U i v ≠ U j v) := by
  classical
  obtain ⟨W,hW,prop⟩ := all_used_four_outer_words hD a ha hfreq
  have hp (j : Coord) := column_permutation_withProfile a W (fun i k => (prop i).2.2 k) j
  choose lab hzero hpattern using hp
  let E := renameDesign (Equiv.refl _) lab D
  let U (i : Coord) : Word 6 := renameWords (Equiv.refl _) lab (W i)
  have hlin := renameDesign_linear hD (Equiv.refl _) lab
  have mem (i : Coord) : U i ∈ E := Finset.mem_map.mpr ⟨W i,(prop i).1,rfl⟩
  have hinj : Function.Injective U := (renameWords (Equiv.refl _) lab).injective.comp hW
  refine ⟨E,hlin,renameDesign_saturated hS _ _,renameDesign_card _ _ _,?_,?_,?_,
    U,hinj,?_,?_,?_⟩
  · refine Finset.mem_map.mpr ⟨a,ha,?_⟩
    funext j
    exact hzero j
  · intro j
    have h := renameDesign_freq (Equiv.refl _) lab D j (a j)
    rw [hzero j] at h
    exact h.trans (hfreq j)
  · intro g b hb
    have keep := renameDesign_freq (Equiv.refl _) lab D g ((lab g).symm b)
    rw [(lab g).apply_symm_apply] at keep
    refine keep.trans (initial g _ ?_)
    intro e
    apply hb
    have e' := congrArg (lab g) e
    rwa [(lab g).apply_symm_apply,hzero g] at e'
  · intro i
    refine ⟨mem i,?_,?_⟩
    · change lab i (W i i) = 0
      rw [(prop i).2.1,hzero i]
    · intro j hj e
      change lab j (W i j) = 0 at e
      rw [← hzero j] at e
      exact (prop i).2.2 j hj ((lab j).injective e)
  · intro j
    have e : outerColumn U j = outerColumn (fun i k => lab j (W i k)) j := rfl
    rw [e]
    exact hpattern j
  · intro i j u v nij nuv e t
    exact nij (hinj (hlin (mem i) (mem j) nuv e t))


theorem all_used_realizes_published_withProfile {D : Design 6} (hD : Linear D)
    (hS : Saturated D) (a : Word 6) (ha : a ∈ D)
    (hfreq : ∀ j, freq D (j,a j) = 2)
    (initial : ∀ (g : Coord) (b : Fin 6), b ≠ a g → freq D (g,b) = 3) :
    ∃ G : Design 6, Linear G ∧ Saturated G ∧ G.card = D.card ∧
      (fun _ => 0) ∈ G ∧ (∀ j, freq G (j,0) = 2) ∧
      (∀ (j : Coord) (b : Fin 6), b ≠ 0 → freq G (j,b) = 3) ∧
      ∃ W : Coord → Word 6,
        (∀ i, W i ∈ G ∧ W i i = 0 ∧ ∀ j ≠ i, W i j ≠ 0) ∧
        actualRowCodes W ∈ published := by
  obtain ⟨E,hE,hsE,hcE,hzE,hlE,regular,U,_,hU,hpat,one⟩ :=
    normalize_all_used_outer_patterns_withProfile hD hS a ha hfreq initial
  have hp' := outerColumns_canonical_published U (fun i => (hU i).2.1) hpat one
  obtain ⟨p,hp,hpn⟩ := canonical_origin_of_published _ hp'
  have hpub : normalize (ofColumns (outerColumns U)) p ∈ published := by rw [hpn]; exact hp'
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
    (renameDesign_card _ _ _).trans (hcF.trans hcE),?_,?_,?_,W,?_,codes ▸ hpub⟩
  · refine Finset.mem_map.mpr ⟨_,hzF,?_⟩
    funext j
    exact fixed j
  · intro j
    have h := renameDesign_freq I lab F j 0
    rw [fixed j] at h
    exact h.trans (hlF j)
  · intro g b hb
    have keepG := renameDesign_freq I lab F g ((lab g).symm b)
    rw [(lab g).apply_symm_apply] at keepG
    have keepF := renameDesign_freq k (fun _ => Equiv.refl _) E g ((lab g).symm b)
    refine keepG.trans (keepF.trans (regular (k g) _ ?_))
    intro e
    apply hb
    have e' := congrArg (lab g) e
    rwa [(lab g).apply_symm_apply,fixed g] at e'
  · intro i
    refine ⟨Finset.mem_map.mpr ⟨_,(hV i).1,rfl⟩,?_,?_⟩
    · change lab i (V i i) = 0
      rw [(hV i).2.1,fixed i]
    · intro j ne h
      change lab j (V i j) = 0 at h
      rw [← fixed j] at h
      exact (hV i).2.2 j ne ((lab j).injective h)


#print axioms all_used_realizes_published_withProfile
end LatinGap
