import FranklMissingDeletionBasic

/- Kernel-checked with pinned Lean 4.36 and Mathlib. -/
namespace FranklForcingFiber
variable {α : Type*} [DecidableEq α]

/-- If B has one strict extension available inside G, adding the deletion
of x from an original A does not create a seven-chain. The lift appends
x exactly to those chain members containing the new set. It is monotone
and can collapse only the unique step where x becomes present. -/
theorem noSevenChain_insert_erase_of_extra_top
    {G B : Finset (Finset α)} {A T : Finset α} {x : α}
    (hG : NoSevenChain G) (hBG : B ⊆ G) (hB : UnionClosed B)
    (hAB : A ∈ B) (hxA : x ∈ A)
    (hTG : T ∈ G) (hT : ∀ ⦃D⦄, D ∈ B → D ⊂ T) :
    NoSevenChain (insert (A.erase x) B) := by
  classical
  let C := A.erase x
  let lift (D : Finset α) := if C ⊆ D then insert x D else D
  have hle (D : Finset α) : D ⊆ lift D := by
    by_cases h : C ⊆ D <;> simp [lift,h]
  have hupper (D : Finset α) : lift D ⊆ insert x D := by
    by_cases h : C ⊆ D <;> simp [lift,h]
  have hmon {D E : Finset α} (hDE : D ⊆ E) : lift D ⊆ lift E := by
    by_cases hCD : C ⊆ D
    · have hCE := hCD.trans hDE
      simp only [lift,hCD,hCE,↓reduceIte]
      intro w hw
      rcases Finset.mem_insert.mp hw with heq | hw
      · exact Finset.mem_insert.mpr (Or.inl heq)
      · exact Finset.mem_insert_of_mem (hDE hw)
    · rw [show lift D = D from by simp [lift,hCD]]
      exact hDE.trans (hle E)
  have hmem {D : Finset α} (hD : D ∈ insert C B) : lift D ∈ B := by
    rcases Finset.mem_insert.mp hD with rfl | hD
    · have hcc : C ⊆ C := fun _ hw => hw
      simpa [lift,hcc,C,Finset.insert_erase hxA] using hAB
    · by_cases hc : C ⊆ D
      · have he : lift D = A ∪ D := by
          rw [show lift D = insert x D from by simp [lift,hc]]
          exact insert_eq_union_of_erase_subset hxA hc
        exact he.symm ▸ hB hAB hD
      · simpa [lift,hc] using hD
  have hstrict {D E : Finset α} (hDE : D ⊂ E)
      (hne : lift D ≠ lift E) : lift D ⊂ lift E :=
    Finset.ssubset_iff_subset_ne.mpr ⟨hmon (Finset.ssubset_iff_subset_ne.mp hDE).1,hne⟩
  have hbad {D E : Finset α} (hDE : D ⊂ E) (he : lift D = lift E) :
      x ∉ D ∧ x ∈ E := by
    have hED : E ⊆ lift D := by
      rw [he]
      exact hle E
    have hEDx : E ⊆ insert x D := hED.trans (hupper D)
    obtain ⟨hsub,hne⟩ := Finset.ssubset_iff_subset_ne.mp hDE
    have hc : ∃ y ∈ E, y ∉ D := by
      by_contra hn
      apply hne
      refine Finset.Subset.antisymm hsub ?_
      intro y hy
      by_contra hy'
      exact hn ⟨y,hy,hy'⟩
    obtain ⟨y,hy,hyn⟩ := hc
    rcases Finset.mem_insert.mp (hEDx hy) with rfl | h
    · exact ⟨hyn,hy⟩
    · exact False.elim (hyn h)
  have htight {D E : Finset α} (hDE : D ⊂ E) (hxD : x ∈ D) :
      lift D ⊂ lift E :=
    hstrict hDE (fun he => (hbad hDE he).1 hxD)
  intro D0 D1 D2 D3 D4 D5 D6 h0 h1 h2 h3 h4 h5 h6 h01 h12 h23 h34 h45 h56
  have m0 := hmem h0
  have m1 := hmem h1
  have m2 := hmem h2
  have m3 := hmem h3
  have m4 := hmem h4
  have m5 := hmem h5
  have m6 := hmem h6
  by_cases e0 : lift D0 = lift D1
  · have x1 := (hbad h01 e0).2
    have x2 := (Finset.ssubset_iff_subset_ne.mp h12).1 x1
    have x3 := (Finset.ssubset_iff_subset_ne.mp h23).1 x2
    have x4 := (Finset.ssubset_iff_subset_ne.mp h34).1 x3
    have x5 := (Finset.ssubset_iff_subset_ne.mp h45).1 x4
    have s1 := htight h12 x1
    have s2 := htight h23 x2
    have s3 := htight h34 x3
    have s4 := htight h45 x4
    have s5 := htight h56 x5
    exact hG (hBG m0) (hBG m2) (hBG m3) (hBG m4) (hBG m5) (hBG m6) hTG
      (by simpa only [e0] using s1) s2 s3 s4 s5 (hT m6)
  have s0 := hstrict h01 e0
  by_cases e1 : lift D1 = lift D2
  · have x2 := (hbad h12 e1).2
    have x3 := (Finset.ssubset_iff_subset_ne.mp h23).1 x2
    have x4 := (Finset.ssubset_iff_subset_ne.mp h34).1 x3
    have x5 := (Finset.ssubset_iff_subset_ne.mp h45).1 x4
    have s2 := htight h23 x2
    have s3 := htight h34 x3
    have s4 := htight h45 x4
    have s5 := htight h56 x5
    exact hG (hBG m0) (hBG m1) (hBG m3) (hBG m4) (hBG m5) (hBG m6) hTG
      s0 (by simpa only [e1] using s2) s3 s4 s5 (hT m6)
  have s1 := hstrict h12 e1
  by_cases e2 : lift D2 = lift D3
  · have x3 := (hbad h23 e2).2
    have x4 := (Finset.ssubset_iff_subset_ne.mp h34).1 x3
    have x5 := (Finset.ssubset_iff_subset_ne.mp h45).1 x4
    have s3 := htight h34 x3
    have s4 := htight h45 x4
    have s5 := htight h56 x5
    exact hG (hBG m0) (hBG m1) (hBG m2) (hBG m4) (hBG m5) (hBG m6) hTG
      s0 s1 (by simpa only [e2] using s3) s4 s5 (hT m6)
  have s2 := hstrict h23 e2
  by_cases e3 : lift D3 = lift D4
  · have x4 := (hbad h34 e3).2
    have x5 := (Finset.ssubset_iff_subset_ne.mp h45).1 x4
    have s4 := htight h45 x4
    have s5 := htight h56 x5
    exact hG (hBG m0) (hBG m1) (hBG m2) (hBG m3) (hBG m5) (hBG m6) hTG
      s0 s1 s2 (by simpa only [e3] using s4) s5 (hT m6)
  have s3 := hstrict h34 e3
  by_cases e4 : lift D4 = lift D5
  · have x5 := (hbad h45 e4).2
    have s5 := htight h56 x5
    exact hG (hBG m0) (hBG m1) (hBG m2) (hBG m3) (hBG m4) (hBG m6) hTG
      s0 s1 s2 s3 (by simpa only [e4] using s5) (hT m6)
  have s4 := hstrict h45 e4
  by_cases e5 : lift D5 = lift D6
  · have x6 := (hbad h56 e5).2
    exact hG (hBG m0) (hBG m1) (hBG m2) (hBG m3) (hBG m4) (hBG m5) hTG
      s0 s1 s2 s3 s4 (hT m5)
  have s5 := hstrict h56 e5
  exact hG (hBG m0) (hBG m1) (hBG m2) (hBG m3) (hBG m4) (hBG m5) (hBG m6)
    s0 s1 s2 s3 s4 s5

#print axioms noSevenChain_insert_erase_of_extra_top
end FranklForcingFiber
