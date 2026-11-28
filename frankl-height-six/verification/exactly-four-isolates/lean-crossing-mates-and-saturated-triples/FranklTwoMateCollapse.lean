import FranklLinkCliqueRegions

/- Static draft, uncompiled. -/
namespace FranklForcingFiber
variable {α : Type*} [DecidableEq α]

def collapseTwoMatePairs (L R : Finset α) (l r x : α) : α :=
  if x ∈ L then l else if x ∈ R then r else x

/-- This retraction identifies exactly the members of each of its two
disjoint mate pairs, and nothing else. In fact the two sets may have
arbitrary cardinalities for this identity. -/
theorem collapseTwoMatePairs_eq_iff {L R : Finset α} {l r x y : α}
    (hDis : Disjoint L R) (hl : l ∈ L) (hr : r ∈ R) :
    collapseTwoMatePairs L R l r x = collapseTwoMatePairs L R l r y ↔
      x = y ∨ (x ∈ L ∧ y ∈ L) ∨ (x ∈ R ∧ y ∈ R) := by
  have hrl : r ∉ L := fun h => (Finset.disjoint_left.mp hDis) h hr
  have hlr : l ∉ R := (Finset.disjoint_left.mp hDis) hl
  have hlne : l ≠ r := fun h => hlr (h.symm ▸ hr)
  constructor
  · intro he
    by_cases hxL : x ∈ L
    · by_cases hyL : y ∈ L
      · exact Or.inr (Or.inl ⟨hxL,hyL⟩)
      · by_cases hyR : y ∈ R
        · exact False.elim (hlne (by simpa [collapseTwoMatePairs,hxL,hyL,hyR] using he))
        · have e : l = y := by simpa [collapseTwoMatePairs,hxL,hyL,hyR] using he
          exact False.elim (hyL (e ▸ hl))
    · by_cases hxR : x ∈ R
      · by_cases hyL : y ∈ L
        · exact False.elim (hlne.symm (by simpa [collapseTwoMatePairs,hxL,hxR,hyL] using he))
        · by_cases hyR : y ∈ R
          · exact Or.inr (Or.inr ⟨hxR,hyR⟩)
          · have e : r = y := by simpa [collapseTwoMatePairs,hxL,hxR,hyL,hyR] using he
            exact False.elim (hyR (e ▸ hr))
      · by_cases hyL : y ∈ L
        · have e : x = l := by simpa [collapseTwoMatePairs,hxL,hxR,hyL] using he
          exact False.elim (hxL (e.symm ▸ hl))
        · by_cases hyR : y ∈ R
          · have e : x = r := by simpa [collapseTwoMatePairs,hxL,hxR,hyL,hyR] using he
            exact False.elim (hxR (e.symm ▸ hr))
          · exact Or.inl (by simpa [collapseTwoMatePairs,hxL,hxR,hyL,hyR] using he)
  · rintro (rfl | ⟨hx,hy⟩ | ⟨hx,hy⟩)
    · rfl
    · simp [collapseTwoMatePairs,hx,hy]
    · have hx' : x ∉ L := fun h => (Finset.disjoint_left.mp hDis) h hx
      have hy' : y ∉ L := fun h => (Finset.disjoint_left.mp hDis) h hy
      simp [collapseTwoMatePairs,hx',hy',hx,hy]

/-- Convenient description of the cyclic exception: each mate pair
from the other matching intersects each of the first matching's pairs. -/
def CrossingMatePairs (L R X Y : Finset α) : Prop :=
  (L ∩ X).Nonempty ∧ (L ∩ Y).Nonempty ∧ (R ∩ X).Nonempty ∧ (R ∩ Y).Nonempty

/-- If the quotient images of two distinct disjoint mate pairs coincide,
and neither has collapsed to a loop, this is the alternating four-cycle.
This lemma is entirely finite and independent of Frankl. -/
theorem crossingMatePairs_of_equal_collapsed_images {L R : Finset α}
    {l r a b c d : α}
    (hLR : Disjoint L R) (hl : l ∈ L) (hr : r ∈ R)
    (hXY : Disjoint ({a,b} : Finset α) {c,d})
    (hAB : collapseTwoMatePairs L R l r a ≠ collapseTwoMatePairs L R l r b)
    (hE : ({collapseTwoMatePairs L R l r a, collapseTwoMatePairs L R l r b} : Finset α) =
      {collapseTwoMatePairs L R l r c, collapseTwoMatePairs L R l r d}) :
    CrossingMatePairs L R {a,b} {c,d} := by
  let f := collapseTwoMatePairs L R l r
  change ({f a,f b} : Finset α) = {f c,f d} at hE
  have hDiff {x y : α} (hx : x ∈ ({a,b} : Finset α)) (hy : y ∈ ({c,d} : Finset α)) : x ≠ y :=
    fun e => (Finset.disjoint_left.mp hXY) hx (e.symm ▸ hy)
  have ha : a ∈ ({a,b} : Finset α) := Finset.mem_insert_self _ _
  have hb : b ∈ ({a,b} : Finset α) := Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have hc : c ∈ ({c,d} : Finset α) := Finset.mem_insert_self _ _
  have hd : d ∈ ({c,d} : Finset α) := Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have matching {x y : α} (hx : x ∈ ({a,b} : Finset α)) (hy : y ∈ ({c,d} : Finset α))
      (he : f x = f y) : (x ∈ L ∧ y ∈ L) ∨ (x ∈ R ∧ y ∈ R) := by
    rcases (collapseTwoMatePairs_eq_iff hLR hl hr).mp he with ee | hh
    · exact False.elim (hDiff hx hy ee)
    · exact hh
  have select (x y : α) (hx : x ∈ ({a,b} : Finset α)) (hy : y ∈ ({a,b} : Finset α))
      (hxy : f x ≠ f y) :
      ∃ u ∈ ({c,d} : Finset α), ∃ v ∈ ({c,d} : Finset α),
        f x = f u ∧ f y = f v := by
    have hFx : f x ∈ ({f a,f b} : Finset α) := by
      simp only [Finset.mem_insert,Finset.mem_singleton] at hx ⊢
      exact hx.imp (congrArg f) (congrArg f)
    have hFy : f y ∈ ({f a,f b} : Finset α) := by
      simp only [Finset.mem_insert,Finset.mem_singleton] at hy ⊢
      exact hy.imp (congrArg f) (congrArg f)
    rw [hE] at hFx hFy
    simp only [Finset.mem_insert,Finset.mem_singleton] at hFx hFy
    rcases hFx with hxc | hxd <;> rcases hFy with hyc | hyd
    · exact False.elim (hxy (hxc.trans hyc.symm))
    · exact ⟨c,hc,d,hd,hxc,hyd⟩
    · exact ⟨d,hd,c,hc,hxd,hyc⟩
    · exact False.elim (hxy (hxd.trans hyd.symm))
  obtain ⟨u,hu,v,hv,heu,hev⟩ := select a b ha hb hAB
  rcases matching ha hu heu with ⟨haL,huL⟩ | ⟨haR,huR⟩ <;>
    rcases matching hb hv hev with ⟨hbL,hvL⟩ | ⟨hbR,hvR⟩
  · exact False.elim (hAB ((collapseTwoMatePairs_eq_iff hLR hl hr).mpr
      (Or.inr (Or.inl ⟨haL,hbL⟩))))
  · exact ⟨⟨a,Finset.mem_inter.mpr ⟨haL,ha⟩⟩,⟨u,Finset.mem_inter.mpr ⟨huL,hu⟩⟩,
      ⟨b,Finset.mem_inter.mpr ⟨hbR,hb⟩⟩,⟨v,Finset.mem_inter.mpr ⟨hvR,hv⟩⟩⟩
  · exact ⟨⟨b,Finset.mem_inter.mpr ⟨hbL,hb⟩⟩,⟨v,Finset.mem_inter.mpr ⟨hvL,hv⟩⟩,
      ⟨a,Finset.mem_inter.mpr ⟨haR,ha⟩⟩,⟨u,Finset.mem_inter.mpr ⟨huR,hu⟩⟩⟩
  · exact False.elim (hAB ((collapseTwoMatePairs_eq_iff hLR hl hr).mpr
      (Or.inr (Or.inr ⟨haR,hbR⟩))))

#print axioms collapseTwoMatePairs_eq_iff
#print axioms crossingMatePairs_of_equal_collapsed_images
end FranklForcingFiber
