import FranklFourDeficitOneAnchors

/- Checked by ordinary pinned Lean with warnings treated as errors. -/
namespace FranklForcingFiber
open FranklBlockIncidence
variable {α : Type*} [DecidableEq α]

/-- A triple through an omitted anchor source links its two mates. -/
theorem mates_link_of_triple {G : Finset (Finset α)} {A : Finset α}
    {p u v : α}
    (hG : NoStrictMajority G) (hm : WeakMinimalGround G)
    (hT : ({p,u,v} : Finset α) ∈ starBlocks G)
    (hpA : p ∈ A) (huA : u ∉ A) (hvA : v ∉ A) (huv : u ≠ v) :
    ({u,v} : Finset α) ∈ blockLinks (sources G) (starBlocks G) A := by
  have hTsub := ((starBlocks_pairDesign hG hm).1 _ hT).1
  have hMate : ({u,v} : Finset α) ⊆ {p,u,v} := by
    intro x hx
    exact Finset.mem_insert_of_mem hx
  apply mem_blockLinks.mpr
  refine ⟨?_,by simp [huv],{p,u,v},hT,hMate,p,Finset.mem_inter.mpr ⟨hpA,by simp⟩⟩
  intro x hx
  have hxn : x ∉ A := by
    simp only [Finset.mem_insert,Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact huA
    · exact hvA
  exact Finset.mem_sdiff.mpr ⟨hTsub (hMate hx),hxn⟩

/-- A pair of disjoint explicit triple blocks through the two chosen
ordinary-pair anchors supplies the two nominal deletions. -/
theorem exact_four_disjointTriple_anchors_full_isolate_omissions
    {G : Finset (Finset α)} {p q u v w z : α} {t : ℕ}
    (hG : NoStrictMajority G) (hm : WeakMinimalGround G)
    (hI : (isolated G).card = 4) (hp : p ∈ sources G) (hq : q ∈ sources G) (hpq : p ≠ q)
    (hdp : designDegree (starBlocks G) p + 2 = (sources G).card)
    (hdq : designDegree (starBlocks G) q + 2 = (sources G).card)
    (hA : omittedStars G (starPairMax G p q) = {p,q})
    (hP : ({p,u,v} : Finset α) ∈ starBlocks G)
    (hQ : ({q,w,z} : Finset α) ∈ starBlocks G)
    (hPt : ({p,u,v} : Finset α).card = 3)
    (hQt : ({q,w,z} : Finset α).card = 3)
    (hDis : Disjoint ({p,u,v} : Finset α) {q,w,z})
    (hN : (starBlocks G).card + 2 * t = (sources G).card.choose 2)
    (htk : 3 * t ≤ (sources G).card) :
    isolated G ⊆ starPairMax G p q ∧
      ∀ x ∈ isolated G, starPairMax G p q \ {x} ∈ avoidBoth G (starLeaf G p) (starLeaf G q) := by
  classical
  let A := omittedStars G (starPairMax G p q)
  have hpA : p ∈ A := (omittedBlock_members hp hq).1
  have hqA : q ∈ A := (omittedBlock_members hp hq).2
  have hDis' := Finset.disjoint_left.mp hDis
  have hA' : A = {p,q} := hA
  have hTwo (a b : α) : ({a,b} : Finset α).card ≤ 2 := by
    simpa only [Finset.card_singleton] using
      (Finset.card_insert_le a ({b} : Finset α))
  have hpu : u ≠ p := by
    intro e
    subst u
    simp at hPt
    exact (Nat.not_le_of_gt (by decide : 3 > 2)) (hPt ▸ hTwo p v)
  have hpv : v ≠ p := by
    intro e
    subst v
    simp at hPt
    exact (Nat.not_le_of_gt (by decide : 3 > 2)) (hPt ▸ hTwo u p)
  have huw : u ≠ q := by intro e; subst u; exact hDis' (a := q) (by simp) (by simp)
  have hvw : v ≠ q := by intro e; subst v; exact hDis' (a := q) (by simp) (by simp)
  have hqw : w ≠ q := by
    intro e
    subst w
    simp at hQt
    exact (Nat.not_le_of_gt (by decide : 3 > 2)) (hQt ▸ hTwo q z)
  have hqz : z ≠ q := by
    intro e
    subst z
    simp at hQt
    exact (Nat.not_le_of_gt (by decide : 3 > 2)) (hQt ▸ hTwo w q)
  have hwp : w ≠ p := by intro e; subst w; exact hDis' (a := p) (by simp) (by simp)
  have hzp : z ≠ p := by intro e; subst z; exact hDis' (a := p) (by simp) (by simp)
  have huv : u ≠ v := by
    intro e
    subst u
    simp at hPt
    exact (Nat.not_le_of_gt (by decide : 3 > 2)) (hPt ▸ hTwo p v)
  have hwz : w ≠ z := by
    intro e
    subst w
    simp at hQt
    exact (Nat.not_le_of_gt (by decide : 3 > 2)) (hQt ▸ hTwo q z)
  have huA : u ∉ A := by rw [hA']; simp [hpu,huw]
  have hvA : v ∉ A := by rw [hA']; simp [hpv,hvw]
  have hwA : w ∉ A := by rw [hA']; simp [hwp,hqw]
  have hzA : z ∉ A := by rw [hA']; simp [hzp,hqz]
  have hLinkP := mates_link_of_triple hG hm hP hpA huA hvA huv
  have hLinkQ := mates_link_of_triple hG hm hQ hqA hwA hzA hwz
  have hDisM : Disjoint ({u,v} : Finset α) {w,z} :=
    Finset.disjoint_left.mpr (fun _ hx hy =>
      hDis' (Finset.mem_insert_of_mem hx) (Finset.mem_insert_of_mem hy))
  obtain ⟨hDel,hDelCard⟩ := linkedDeletion_of_two_disjoint_links hLinkP hLinkQ hDisM
  exact exact_four_two_deficitOne_anchors_full_isolate_omissions hG hm hI hp hq hpq hdp hdq
    hA hDel hDelCard hN htk

#print axioms mates_link_of_triple
#print axioms exact_four_disjointTriple_anchors_full_isolate_omissions
end FranklForcingFiber
