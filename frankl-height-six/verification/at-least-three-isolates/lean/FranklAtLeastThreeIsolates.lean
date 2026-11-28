import FranklPairSignatureSauer
import FranklExcludeThirteenStars
import FranklFewIsolates
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

open scoped BigOperators
namespace FranklBlockIncidence
variable {α : Type*} [DecidableEq α]

def designDegree (B : Finset (Finset α)) (v : α) : Nat := (B.filter (v ∈ ·)).card

theorem pair_design_sum_choose_eq {S : Finset α} {B : Finset (Finset α)}
    (hD : PairDesign S B) : (∑ A ∈ B, A.card.choose 2) = S.card.choose 2 := by
  classical
  have hU : B.biUnion (fun A => A.powersetCard 2) = S.powersetCard 2 := by
    ext R
    constructor
    · intro hR
      obtain ⟨A,hA,hRA⟩ := Finset.mem_biUnion.mp hR
      obtain ⟨hs,hc⟩ := Finset.mem_powersetCard.mp hRA
      exact Finset.mem_powersetCard.mpr ⟨hs.trans (hD.1 A hA).1,hc⟩
    · intro hR
      obtain ⟨hs,hc⟩ := Finset.mem_powersetCard.mp hR
      obtain ⟨a,b,hab,rfl⟩ := Finset.card_eq_two.mp hc
      have ha : a ∈ S := hs (by simp)
      have hb : b ∈ S := hs (by simp)
      obtain ⟨A,⟨hA,haA,hbA⟩,_⟩ := hD.2 a ha b hb hab
      exact Finset.mem_biUnion.mpr ⟨A,hA,Finset.mem_powersetCard.mpr
        ⟨Finset.insert_subset_iff.mpr ⟨haA,Finset.singleton_subset_iff.mpr hbA⟩,by simp [hab]⟩⟩
  have hDisj : (B : Set (Finset α)).PairwiseDisjoint (fun A => A.powersetCard 2) := by
    intro A hA C hC hne
    apply Finset.disjoint_left.mpr
    intro R hRA hRC
    obtain ⟨hs,hc⟩ := Finset.mem_powersetCard.mp hRA
    obtain ⟨hs',_⟩ := Finset.mem_powersetCard.mp hRC
    obtain ⟨a,b,hab,rfl⟩ := Finset.card_eq_two.mp hc
    have ha : a ∈ A := hs (by simp)
    have hb : b ∈ A := hs (by simp)
    have ha' : a ∈ C := hs' (by simp)
    have hb' : b ∈ C := hs' (by simp)
    obtain ⟨_,_,hUnique⟩ := hD.2 a ((hD.1 A hA).1 ha) b ((hD.1 A hA).1 hb) hab
    exact hne ((hUnique _ ⟨hA,ha,hb⟩).trans (hUnique _ ⟨hC,ha',hb'⟩).symm)
  have he := Finset.card_biUnion hDisj
  rw [hU,Finset.card_powersetCard] at he
  simpa only [Finset.card_powersetCard] using he.symm

theorem designDegree_le_card_sub_one {S : Finset α} {B : Finset (Finset α)} {v : α}
    (hD : PairDesign S B) (hv : v ∈ S) : designDegree B v ≤ S.card-1 := by
  classical
  let D := B.filter (v ∈ ·)
  have hU : D.biUnion (fun A => A.erase v) = S.erase v := by
    ext u
    constructor
    · intro hu
      obtain ⟨A,hA,huA⟩ := Finset.mem_biUnion.mp hu
      obtain ⟨hAB,_⟩ := Finset.mem_filter.mp hA
      obtain ⟨hne,h⟩ := Finset.mem_erase.mp huA
      exact Finset.mem_erase.mpr ⟨hne,(hD.1 A hAB).1 h⟩
    · intro hu
      obtain ⟨hvn,huS⟩ := Finset.mem_erase.mp hu
      obtain ⟨A,⟨hAB,hvA,huA⟩,_⟩ := hD.2 v hv u huS hvn.symm
      exact Finset.mem_biUnion.mpr ⟨A,Finset.mem_filter.mpr ⟨hAB,hvA⟩,
        Finset.mem_erase.mpr ⟨hvn,huA⟩⟩
  have hDisj : (D : Set (Finset α)).PairwiseDisjoint (fun A => A.erase v) := by
    intro A hA C hC hne
    apply Finset.disjoint_left.mpr
    intro u huA huC
    obtain ⟨hAB,hvA⟩ := Finset.mem_filter.mp hA
    obtain ⟨hCB,hvC⟩ := Finset.mem_filter.mp hC
    obtain ⟨hvu,huA'⟩ := Finset.mem_erase.mp huA
    obtain ⟨_,huC'⟩ := Finset.mem_erase.mp huC
    obtain ⟨_,_,hUnique⟩ := hD.2 v hv u ((hD.1 A hAB).1 huA') hvu.symm
    exact hne ((hUnique _ ⟨hAB,hvA,huA'⟩).trans (hUnique _ ⟨hCB,hvC,huC'⟩).symm)
  have he := Finset.card_biUnion hDisj
  rw [hU] at he

  have hl : D.card ≤ ∑ A ∈ D, (A.erase v).card := by
    rw [Finset.card_eq_sum_ones]
    apply Finset.sum_le_sum
    intro A hA
    obtain ⟨hAB,hvA⟩ := Finset.mem_filter.mp hA
    have h1 := (hD.1 A hAB).2
    have h2 := Finset.card_erase_add_one hvA
    omega
  rw [← he] at hl
  have hvC := Finset.card_erase_add_one hv
  change D.card ≤ S.card - 1
  exact Nat.le_sub_one_of_lt (by omega)

theorem away_and_two_designDegrees {S : Finset α} {B : Finset (Finset α)} {p q : α}
    (hD : PairDesign S B) (hp : p ∈ S) (hq : q ∈ S) (hpq : p ≠ q) :
    (away B p q).card + designDegree B p + designDegree B q = B.card + 1 := by
  classical
  let P := B.filter (p ∈ ·)
  let Q := B.filter (q ∈ ·)
  obtain ⟨A,⟨hAB,hpA,hqA⟩,hu⟩ := hD.2 p hp q hq hpq
  have hi : P ∩ Q = {A} := by
    ext C
    constructor
    · intro hc
      obtain ⟨hP,hQ⟩ := Finset.mem_inter.mp hc
      exact Finset.mem_singleton.mpr (hu C ⟨(Finset.mem_filter.mp hP).1,
        (Finset.mem_filter.mp hP).2,(Finset.mem_filter.mp hQ).2⟩)
    · intro hc
      have he := Finset.mem_singleton.mp hc
      subst C
      exact Finset.mem_inter.mpr ⟨Finset.mem_filter.mpr ⟨hAB,hpA⟩,Finset.mem_filter.mpr ⟨hAB,hqA⟩⟩
  have hA : away B p q = B \ (P ∪ Q) := by
    ext C
    simp only [mem_away,Finset.mem_sdiff,Finset.mem_union,P,Q,Finset.mem_filter]
    tauto
  have hs : P ∪ Q ⊆ B := Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  have hW := Finset.card_sdiff_add_card_eq_card hs
  rw [← hA] at hW
  have hU := Finset.card_union_add_card_inter P Q
  rw [hi,Finset.card_singleton] at hU

  change (away B p q).card + P.card + Q.card = B.card + 1
  omega

theorem sum_designDegree {S : Finset α} {B : Finset (Finset α)}
    (hD : PairDesign S B) : (∑ v ∈ S, designDegree B v) = ∑ A ∈ B, A.card := by
  classical
  let T := B
  calc
    (∑ v ∈ S, designDegree B v) = ∑ v ∈ S, ∑ A ∈ T, if v ∈ A then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro v _
      exact Finset.card_filter _ _
    _ = ∑ A ∈ T, ∑ v ∈ S, if v ∈ A then 1 else 0 := Finset.sum_comm
    _ = ∑ A ∈ T, A.card := by
      apply Finset.sum_congr rfl
      intro A hA
      have hAB : A ∈ B := hA
      have he : S.filter (· ∈ A) = A := by
        ext x
        exact ⟨fun h => (Finset.mem_filter.mp h).2,fun h => Finset.mem_filter.mpr ⟨(hD.1 A hAB).1 h,h⟩⟩
      rw [← Finset.card_filter,he]


theorem two_mul_choose_eq_mul_pred (n : Nat) : 2*n.choose 2 = n*(n-1) := by
  rw [Nat.choose_two_right, Nat.mul_div_cancel' n.even_mul_pred_self.two_dvd]

/-- A lower bound on all block incidences is controlled by the total blocks
of a finite pair design. This is the degree-average Cauchy bound in Nat. -/
theorem min_degree_choose_succ_le_block_card {S : Finset α} {B : Finset (Finset α)} {g : Nat}
    (hD : PairDesign S B) (hg : 1 ≤ g) (hgk : g ≤ S.card-1)
    (hm : ∀ v ∈ S, g ≤ designDegree B v) : (g+1).choose 2 ≤ B.card := by
  let k := S.card
  let N := B.card
  let P := k*(k-1)
  let T := ∑ A ∈ B, A.card
  let x := k*g
  have hk : 0 < k := by omega
  have hxT : x ≤ T := by
    have h := Finset.sum_le_sum (s := S) hm
    have hc : (∑ _v ∈ S, g) = S.card*g := Finset.sum_const_nat (fun _ _ => rfl)
    rw [hc,sum_designDegree hD] at h
    exact h
  have hQ : (∑ A ∈ B, A.card^2) = P+T := by
    calc
      _ = ∑ A ∈ B, (2*A.card.choose 2 + A.card) := by
        apply Finset.sum_congr rfl
        intro A hA
        have hs : 1 ≤ A.card := by have h := (hD.1 A hA).2; omega
        calc
          _ = A.card * (A.card - 1 + 1) := by rw [Nat.sub_add_cancel hs, pow_two]
          _ = _ := by rw [Nat.mul_add, Nat.mul_one, two_mul_choose_eq_mul_pred]
      _ = P+T := by
        rw [Finset.sum_add_distrib,← Finset.mul_sum,pair_design_sum_choose_eq hD,two_mul_choose_eq_mul_pred]
  have hC : T^2 ≤ N*(P+T) := by
    rw [← hQ]
    simpa [T,N] using (Finset.sum_mul_sq_le_sq_mul_sq (R := Nat) B 1 (fun A => A.card))
  have hxx : x^2 ≤ T^2 := Nat.pow_le_pow_left hxT 2
  have hpoly : x^2*(P+T) ≤ T^2*(P+x) := by
    have h1 := Nat.mul_le_mul_right P hxx
    have h2 : x^2*T ≤ T^2*x := by
      calc
        _ = (x*T)*x := by ring
        _ ≤ (x*T)*T := Nat.mul_le_mul_left _ hxT
        _ = _ := by ring
    simpa only [Nat.mul_add] using Nat.add_le_add h1 h2
  have hF : x^2 ≤ N*(P+x) := by
    have h := hpoly.trans (Nat.mul_le_mul_right (P+x) hC)
    have h' : (P+T)*x^2 ≤ (P+T)*(N*(P+x)) := by
      simpa only [mul_assoc,mul_left_comm,mul_comm] using h
    have hxpos : 0 < x := Nat.mul_pos hk (by omega)
    exact Nat.le_of_mul_le_mul_left h' (by omega)
  have hK : k*g^2 ≤ N*(k-1+g) := by
    have he : P+x = k*(k-1+g) := by dsimp [P,x]; ring
    rw [he] at hF
    have h' : k*(k*g^2) ≤ k*(N*(k-1+g)) := by
      convert hF using 1 <;> (try dsimp [x]) <;> ring
    exact Nat.le_of_mul_le_mul_left h' hk
  let u := k-1-g
  have hku : k-1 = g+u := by dsimp [u]; omega
  have hku' : k = g+u+1 := by omega
  have hgu : u ≤ g*u := by
    simpa using Nat.mul_le_mul_right u hg
  have hprod : (g+1)*(k-1+g) ≤ 2*k*g := by
    rw [hku,hku']
    calc
      _ = (2*g*g+2*g+g*u)+u := by ring
      _ ≤ (2*g*g+2*g+g*u)+g*u := Nat.add_le_add_left hgu _
      _ = _ := by ring
  have hgg : g*(g+1) ≤ 2*N := by
    have h1 := (Nat.mul_le_mul_left g hprod).trans (show g*(2*k*g) ≤ (2*N)*(k-1+g) by
      convert Nat.mul_le_mul_left 2 hK using 1 <;> ring)
    have h2 : (k-1+g)*(g*(g+1)) ≤ (k-1+g)*(2*N) := by
      convert h1 using 1 <;> ring
    exact Nat.le_of_mul_le_mul_left h2 (by omega)
  have hc := two_mul_choose_eq_mul_pred (g+1)
  change 2*(g+1).choose 2 = (g+1)*g at hc
  rw [Nat.mul_comm (g+1) g] at hc
  change (g+1).choose 2 ≤ N
  omega

#print axioms min_degree_choose_succ_le_block_card

end FranklBlockIncidence

namespace FranklForcingFiber
open FranklBlockIncidence
variable {α : Type*} [DecidableEq α]

/-- The outsider signature classes are coarser than the groups through
any chosen center of the fixed block. -/
theorem pair_signatures_card_lt_designDegree {G : Finset (Finset α)}
    {A : Finset α} {p q : α}
    (hG : NoStrictMajority G) (hmin : WeakMinimalGround G)
    (hp : p ∈ sources G) (hq : q ∈ sources G) (hpq : p ≠ q)
    (hpA : p ∈ A) (hqA : q ∈ A) (hAB : A ∈ starBlocks G)
    (hEq : A = omittedStars G (starPairMax G p q)) :
    let K := compressPair G p q (starLeaf G p) (starLeaf G q)
    (((sources G \ A).image (signature K)).card) < designDegree (starBlocks G) p := by
  classical
  let B := starBlocks G
  let E := sources G \ A
  let K := compressPair G p q (starLeaf G p) (starLeaf G q)
  let f := signature K
  let D := groupsThrough B A p
  have hD := starBlocks_pairDesign hG hmin
  have hcover : (E.image f) ⊆ D.biUnion (fun T => (T \ A).image f) := by
    intro g hg
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hg
    obtain ⟨hxS,hxA⟩ := Finset.mem_sdiff.mp hx
    have hpx : p ≠ x := fun e => hxA (e ▸ hpA)
    obtain ⟨T,⟨hTB,hpT,hxT⟩,_⟩ := hD.2 p hp x hxS hpx
    have hne : T ≠ A := fun e => hxA (e ▸ hxT)
    exact Finset.mem_biUnion.mpr ⟨T,Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hne,hTB⟩,hpT⟩,
      Finset.mem_image_of_mem f (Finset.mem_sdiff.mpr ⟨hxT,hxA⟩)⟩
  have hc : ∀ T ∈ D, ((T \ A).image f).card ≤ 1 := by
    intro T hT
    apply Finset.card_le_one_iff.mpr
    intro x y hx hy
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hy
    by_cases hne : u = v
    · subst v
      rfl
    · obtain ⟨hTe,hpT⟩ := Finset.mem_filter.mp hT
      have hTB := (Finset.mem_erase.mp hTe).2
      have huvT : ({u,v} : Finset α) ⊆ T := Finset.insert_subset_iff.mpr
        ⟨(Finset.mem_sdiff.mp hu).1,Finset.singleton_subset_iff.mpr (Finset.mem_sdiff.mp hv).1⟩
      have hEs : T \ A ⊆ E := by
        intro z hz
        obtain ⟨hzT,hzA⟩ := Finset.mem_sdiff.mp hz
        exact Finset.mem_sdiff.mpr ⟨(hD.1 T hTB).1 hzT,hzA⟩
      have hLink : ({u,v} : Finset α) ∈ blockLinks (sources G) B A :=
        mem_blockLinks.mpr ⟨(Finset.insert_subset_iff.mpr ⟨hu,Finset.singleton_subset_iff.mpr hv⟩).trans hEs,
          by simp [hne],T,hTB,huvT,⟨p,Finset.mem_inter.mpr ⟨hpA,hpT⟩⟩⟩
      exact compressed_pair_signatures_eq_of_blockLink hG hmin hp hq hpq hpA hqA hEq hLink (by simp) (by simp)
  have hSum : (E.image f).card ≤ D.card := by
    calc
      _ ≤ (D.biUnion (fun T => (T \ A).image f)).card := Finset.card_le_card hcover
      _ ≤ ∑ T ∈ D, ((T \ A).image f).card := Finset.card_biUnion_le
      _ ≤ ∑ _T ∈ D, 1 := Finset.sum_le_sum hc
      _ = D.card := (Finset.card_eq_sum_ones D).symm
  have he : D = (B.filter (p ∈ ·)).erase A := by
    ext T
    simp only [D,groupsThrough,Finset.mem_filter,Finset.mem_erase]
    tauto
  have hAd : A ∈ B.filter (p ∈ ·) := Finset.mem_filter.mpr ⟨hAB,hpA⟩
  rw [he] at hSum
  have hcard := Finset.card_erase_add_one hAd
  change (E.image f).card < (B.filter (p ∈ ·)).card
  omega

/-- All ground-minimal weak height-six counterexamples would need at least
three isolated points, including when there are no forcing edges. -/
theorem three_le_isolated_of_weakMinimalGround {G : Finset (Finset α)}
    (hG : NoStrictMajority G) (hmin : WeakMinimalGround G) : 3 ≤ (isolated G).card := by
  classical
  by_contra! ht
  have hk : 2 ≤ (sources G).card := by
    by_contra! hksmall
    by_cases h0 : (sources G).card = 0
    · have hSempty := Finset.card_eq_zero.mp h0
      have hLempty : leaves G = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro x hx
        obtain ⟨p,hp,hpx,hF⟩ := (mem_leaves.mp hx).2
        have hpS : p ∈ sources G := mem_sources.mpr ⟨hp,x,hpx,hF⟩
        rw [hSempty] at hpS
        exact Finset.notMem_empty _ hpS
      have hIg : isolated G = ground G := by simp [isolated,hSempty,hLempty]
      have hsmall : (ground G).card ≤ 2 := by rw [← hIg]; omega
      have hAll (A : Finset α) (hA : A ∈ G) : A = ground G := by
        have h2 : 2 ≤ A.card := by
          have hpos := Finset.card_pos.mpr (hG.2.1 hA)
          by_contra! hc
          obtain ⟨x,rfl⟩ := Finset.card_eq_one.mp (show A.card = 1 by omega)
          exact weak_no_singleton hG x hA
        exact Finset.eq_of_subset_of_card_le (subset_ground hA) (hsmall.trans h2)
      obtain ⟨A,hA⟩ := hG.1
      obtain ⟨x,hx⟩ := hG.2.1 hA
      have hxG := subset_ground hA hx
      have he : G.filter (x ∈ ·) = G := Finset.filter_eq_self.mpr (fun C hC => (hAll C hC).symm ▸ hxG)
      have hf := hG.2.2.2.2 x
      rw [frequency,he] at hf
      have hpos := Finset.card_pos.mpr hG.1
      omega
    · obtain ⟨p,he⟩ := Finset.card_eq_one.mp (show (sources G).card = 1 by omega)
      have hp : p ∈ sources G := he.symm ▸ Finset.mem_singleton_self p
      have hh := unique_source_isolated_card_ge_three hG hmin hp (fun q hq => by
        rw [he] at hq
        exact Finset.mem_singleton.mp hq)
      omega
  let S := sources G
  let B := starBlocks G
  have hD : PairDesign S B := starBlocks_pairDesign hG hmin
  change 2 ≤ S.card at hk
  have hS : S.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨p,hp,hpMin⟩ := Finset.exists_min_image S (designDegree B) hS
  have hpc := Finset.card_erase_add_one hp
  obtain ⟨q,hqe⟩ := Finset.card_pos.mp (show 0 < (S.erase p).card by omega)
  obtain ⟨hqp,hq⟩ := Finset.mem_erase.mp hqe
  have hpq := hqp.symm
  obtain ⟨A,⟨hAB,hpA,hqA⟩,_⟩ := hD.2 p hp q hq hpq
  have hEq := block_eq_omitted_for_member_pair hG hmin hAB hpA hqA hpq
  have hSig := pair_signatures_card_lt_designDegree hG hmin hp hq hpq hpA hqA hAB hEq
  have hUpper := pair_fiber_card_le_sauer_block_signatures hG hmin hp hq hpq hEq
  let g := designDegree B p
  have hg : 1 ≤ g := Finset.card_pos.mpr ⟨A,Finset.mem_filter.mpr ⟨hAB,hpA⟩⟩
  have hgk := designDegree_le_card_sub_one hD hp
  have hqk := designDegree_le_card_sub_one hD hq
  have hChoice := min_degree_choose_succ_le_block_card hD hg hgk hpMin
  let K := compressPair G p q (starLeaf G p) (starLeaf G q)
  let m := ( (S \ A).image (signature K) ).card + (isolated G).card
  have hm : m ≤ g+1 := by
    change ((S \ A).image (signature K)).card < g at hSig
    dsimp [m]
    omega
  have hCh := Nat.choose_le_choose 2 hm
  change (avoidBoth G (starLeaf G p) (starLeaf G q)).card ≤ 1+m+m.choose 2 at hUpper
  have hLow := leaf_pair_count_with_blocks hG hmin hp hq hpq
  have hW := away_and_two_designDegrees hD hp hq hpq
  have hPart := partition_card hG hmin
  have hL := sources_card_le_leaves hG hmin
  change g ≤ S.card - 1 at hgk
  change designDegree B q ≤ S.card - 1 at hqk
  change (g+1).choose 2 ≤ B.card at hChoice
  change (ground G).card = (isolated G).card + S.card + (leaves G).card at hPart
  change S.card ≤ (leaves G).card at hL
  change (ground G).card + S.card + (away B p q).card ≤ _ at hLow
  change (away B p q).card + g + designDegree B q = B.card+1 at hW
  omega

#print axioms pair_signatures_card_lt_designDegree
#print axioms three_le_isolated_of_weakMinimalGround
end FranklForcingFiber
