import EulerLexMinimum
import EulerAllUsedNonLexGeometry

namespace LatinGap.PairEncoding
open EulerAllUsedDiagrams

noncomputable def geometricIncidence (D : Design 6) : IncidenceSystem :=
  fun g a b => (encode D).pair (degreeNeighborPair g a b)

theorem geometricIncidence_transpose (D : Design 6) (a b : Fin 6) :
    geometricIncidence D 1 b a = geometricIncidence D 0 a b := rfl

private theorem geometricIncidence_iff (D : Design 6) (g : Coord) (a b : Fin 6) :
    geometricIncidence D g a b = true ↔ Used D (g,a) (degreePartner g,b) := by
  unfold geometricIncidence degreeNeighborPair
  split
  · exact pair_encode D _
  · exact (pair_encode D _).trans ⟨used_symm,used_symm⟩

private theorem relabel_used (D : Design 6) (p : LabelPerms) (i j : Coord) (a b : Fin 6) :
    Used (renameDesign (Equiv.refl _) (fun g => (p g).symm) D) (i,a) (j,b) ↔
      Used D (i,p i a) (j,p j b) := by
  constructor
  · rintro ⟨n,w,hw,h1,h2⟩
    obtain ⟨u,hu,rfl⟩ := Finset.mem_map.mp hw
    refine ⟨n,u,hu,?_,?_⟩
    · change (p i).symm (u i)=a at h1
      have e := congrArg (p i) h1
      simpa using e
    · change (p j).symm (u j)=b at h2
      have e := congrArg (p j) h2
      simpa using e
  · rintro ⟨n,u,hu,h1,h2⟩
    refine ⟨n,renameWords (Equiv.refl _) (fun g => (p g).symm) u,
      Finset.mem_map.mpr ⟨u,hu,rfl⟩,?_,?_⟩
    · change (p i).symm (u i)=a
      rw [show u i=p i a from h1,(p i).symm_apply_apply]
    · change (p j).symm (u j)=b
      rw [show u j=p j b from h2,(p j).symm_apply_apply]

theorem geometricIncidence_relabel (D : Design 6) (p : LabelPerms) (g : Coord) (a b : Fin 6) :
    geometricIncidence (renameDesign (Equiv.refl _) (fun j => (p j).symm) D) g a b =
      pullIncidence (geometricIncidence D) p g a b := by
  apply Bool.eq_iff_iff.mpr
  change _ ↔ geometricIncidence D g (p g a) (p (degreePartner g) b)=true
  rw [geometricIncidence_iff, geometricIncidence_iff]
  exact relabel_used D p g (degreePartner g) a b

private theorem left_le_foldmax (xs : List Nat) (init : Nat) :
    init ≤ xs.foldl max init := by
  induction xs generalizing init with
  | nil => rfl
  | cons x xs ih => exact (Nat.le_max_left _ _).trans (ih _)

private theorem member_le_foldmax {x : Nat} {xs : List Nat} (h : x ∈ xs) (init : Nat) :
    x ≤ xs.foldl max init := by
  induction xs generalizing init with
  | nil => contradiction
  | cons a as ih =>
    rcases List.mem_cons.mp h with rfl | h
    · exact (Nat.le_max_right _ _).trans (left_le_foldmax _ _)
    · exact ih h _

theorem pins_below_prefix (W : Coord → Word 6) (i g : Coord) :
    (W i g).val < archivePinnedPrefix (actualRowCodes W) g := by
  have hex : (decimalWord (decimalCode (W i)) g).val ∈
      (actualRowCodes W).map (fun n => (decimalWord n g).val) :=
    List.mem_map.mpr ⟨_, by rw [actualRowCodes_eq]; exact List.mem_ofFn.mpr ⟨i,rfl⟩, rfl⟩
  have b := member_le_foldmax hex 1
  rw [decimalWord_decimalCode] at b
  exact Nat.lt_succ_of_le b

theorem archivePinnedPrefix_pos (codes : List Nat) (g : Coord) :
    0 < archivePinnedPrefix codes g := Nat.zero_lt_succ _

theorem archiveLexLabelPairs_range {codes : List Nat} {g : Coord} {a b : Fin 6}
    (h : (a,b) ∈ archiveLexLabelPairs codes g) :
    archivePinnedPrefix codes g ≤ a.val ∧ a<b := by
  obtain ⟨⟨k,hk⟩,_,eq⟩ := List.mem_map.mp h
  have fromFirst := congrArg (fun p : Fin 6 × Fin 6 => p.1.val) eq
  have fromSecond := congrArg (fun p : Fin 6 × Fin 6 => p.2.val) eq
  change archivePinnedPrefix codes g + k = a.val at fromFirst
  change archivePinnedPrefix codes g + k + 1 = b.val at fromSecond
  change _ ∧ a.val<b.val
  omega

/-- Simultaneous incidence sorting preserves the exact pinned words and
the normalized degree profile; only unpinned labels are permuted. -/
theorem normalize_geometry_allUsed_lex {D : Design 6} (lin : Linear D) (sat : Saturated D)
    (zero : (fun _ => 0) ∈ D)
    (profile : ∀ (g : Coord) (a : Fin 6), freq D (g,a) = if a=0 then 2 else 3)
    (W : Coord → Word 6) (hw : ∀ i, W i ∈ D) :
    ∃ G : Design 6, Linear G ∧ Saturated G ∧ G.card=D.card ∧
      (fun _=>0) ∈ G ∧ (∀ (g : Coord) (a : Fin 6), freq G (g,a) = if a=0 then 2 else 3) ∧
      (∀ i, W i ∈ G) ∧
      ∀ g a b, (a,b) ∈ archiveLexLabelPairs (actualRowCodes W) g →
        firstDifferenceOrder (geometricIncidence G g) a b := by
  let starts := archivePinnedPrefix (actualRowCodes W)
  obtain ⟨p,hfix,horders⟩ :=
    exists_simultaneous_lex (geometricIncidence D) starts (geometricIncidence_transpose D)
  let I : Coord ≃ Coord := Equiv.refl _
  let lab : LabelPerms := fun g => (p g).symm
  let G := renameDesign I lab D
  have fixes (g : Coord) (a : Fin 6) (h : a.val<starts g) : lab g a=a :=
    (p g).injective (by change p g ((p g).symm a)=p g a; rw [(p g).apply_symm_apply,hfix g a h])
  have pzero (g : Coord) : p g 0=0 := hfix g 0 (archivePinnedPrefix_pos _ _)
  refine ⟨G,renameDesign_linear lin _ _,renameDesign_saturated sat _ _,
    renameDesign_card _ _ _,?_,?_,?_,?_⟩
  · refine Finset.mem_map.mpr ⟨_,zero,?_⟩
    funext g
    exact fixes g 0 (archivePinnedPrefix_pos _ _)
  · intro g a
    have keep := renameDesign_freq I lab D g (p g a)
    change freq G (g,(p g).symm (p g a)) = freq D (g,p g a) at keep
    rw [(p g).symm_apply_apply,profile] at keep
    have iffzero : p g a=0 ↔ a=0 := by
      constructor
      · intro h; exact (p g).injective (h.trans (pzero g).symm)
      · intro h; subst a; exact pzero g
    simpa only [iffzero] using keep
  · intro i
    refine Finset.mem_map.mpr ⟨W i,hw i,?_⟩
    funext g
    exact fixes g (W i g) (pins_below_prefix W i g)
  · intro g a b h
    obtain ⟨bound,lt⟩ := archiveLexLabelPairs_range h
    have e : geometricIncidence G g = pullIncidence (geometricIncidence D) p g := by
      funext a' b'
      exact geometricIncidence_relabel D p g a' b'
    rw [e]
    exact horders g a b bound lt

#print axioms geometricIncidence_relabel
#print axioms normalize_geometry_allUsed_lex
end LatinGap.PairEncoding
