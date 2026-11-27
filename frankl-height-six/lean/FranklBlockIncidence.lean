import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Data.Finset.Powerset

open scoped BigOperators

namespace FranklBlockIncidence
variable {α : Type*} [DecidableEq α]

/-- A finite pair design: every two distinct points lie in a unique block. -/
def PairDesign (S : Finset α) (B : Finset (Finset α)) : Prop :=
  (∀ A ∈ B, A ⊆ S ∧ 2 ≤ A.card) ∧
  ∀ p ∈ S, ∀ q ∈ S, p ≠ q → ∃! A, A ∈ B ∧ p ∈ A ∧ q ∈ A

noncomputable def away (B : Finset (Finset α)) (p q : α) : Finset (Finset α) := by
  classical
  exact B.filter (fun A => p ∉ A ∧ q ∉ A)

theorem mem_away {B : Finset (Finset α)} {p q : α} {A : Finset α} :
    A ∈ away B p q ↔ A ∈ B ∧ p ∉ A ∧ q ∉ A := by
  classical
  exact Finset.mem_filter

/-- Count the blocks avoiding two fixed points by covering the potential
neighbours of each other point, then double-counting incidences. -/
theorem away_card_mul_lower {S : Finset α} {B : Finset (Finset α)} {p q : α}
    (hD : PairDesign S B) (hp : p ∈ S) (hq : q ∈ S) (hpq : p ≠ q)
    {r d : ℕ} (hr : ∀ A ∈ B, A.card ≤ r)
    (hGap : (r - 1) * (d - 1) + 2 * (r - 2) < S.card - 3) :
    (S.card - 2) * d ≤ (away B p q).card * r := by
  classical
  let E := (S.erase p).erase q
  let W := away B p q
  let deg (v : α) := (W.filter (v ∈ ·)).card
  have hEcard : E.card = S.card - 2 := by
    have hpC := Finset.card_erase_add_one hp
    have hqC := Finset.card_erase_add_one (Finset.mem_erase.mpr ⟨hpq.symm,hq⟩)
    change E.card + 1 = (S.erase p).card at hqC
    omega
  have hE (v : α) (hv : v ∈ E) : v ∈ S ∧ v ≠ p ∧ v ≠ q := by
    obtain ⟨hvq,hv'⟩ := Finset.mem_erase.mp hv
    obtain ⟨hvp,hvS⟩ := Finset.mem_erase.mp hv'
    exact ⟨hvS,hvp,hvq⟩
  have hdeg (v : α) (hv : v ∈ E) : d ≤ deg v := by
    obtain ⟨hvS,hvp,hvq⟩ := hE v hv
    obtain ⟨P,⟨hPB,hvP,hpP⟩,hPU⟩ := hD.2 v hvS p hp hvp
    obtain ⟨Q,⟨hQB,hvQ,hqQ⟩,hQU⟩ := hD.2 v hvS q hq hvq
    let A := (P.erase v).erase p
    let C := (Q.erase v).erase q
    let Z := (W.filter (v ∈ ·)).biUnion (fun T => T.erase v)
    have hcover : E.erase v ⊆ (Z ∪ A) ∪ C := by
      intro u hu
      obtain ⟨huv,huE⟩ := Finset.mem_erase.mp hu
      obtain ⟨huS,hup,huq⟩ := hE u huE
      obtain ⟨T,⟨hTB,hvT,huT⟩,_⟩ := hD.2 v hvS u huS huv.symm
      by_cases hpT : p ∈ T
      · have he := hPU T ⟨hTB,hvT,hpT⟩
        have huP : u ∈ P := he ▸ huT
        exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr
          (Or.inr (Finset.mem_erase.mpr ⟨hup,Finset.mem_erase.mpr ⟨huv,huP⟩⟩))))
      · by_cases hqT : q ∈ T
        · have he := hQU T ⟨hTB,hvT,hqT⟩
          have huQ : u ∈ Q := he ▸ huT
          exact Finset.mem_union.mpr (Or.inr (Finset.mem_erase.mpr ⟨huq,Finset.mem_erase.mpr ⟨huv,huQ⟩⟩))
        · have hTW : T ∈ W := mem_away.mpr ⟨hTB,hpT,hqT⟩
          have huZ : u ∈ Z := Finset.mem_biUnion.mpr
            ⟨T,Finset.mem_filter.mpr ⟨hTW,hvT⟩,Finset.mem_erase.mpr ⟨huv,huT⟩⟩
          exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl huZ)))
    have hAc : A.card ≤ r-2 := by
      have h1 := Finset.card_erase_add_one hvP
      have h2 := Finset.card_erase_add_one (Finset.mem_erase.mpr ⟨hvp.symm,hpP⟩)
      change A.card + 1 = (P.erase v).card at h2
      have h := hr P hPB
      omega
    have hCc : C.card ≤ r-2 := by
      have h1 := Finset.card_erase_add_one hvQ
      have h2 := Finset.card_erase_add_one (Finset.mem_erase.mpr ⟨hvq.symm,hqQ⟩)
      change C.card + 1 = (Q.erase v).card at h2
      have h := hr Q hQB
      omega
    have hZc : Z.card ≤ (r-1)*deg v := by
      calc
        Z.card ≤ ∑ T ∈ W.filter (v ∈ ·), (T.erase v).card := Finset.card_biUnion_le
        _ ≤ ∑ _T ∈ W.filter (v ∈ ·), (r-1) := by
          apply Finset.sum_le_sum
          intro T hT
          obtain ⟨hTW,hvT⟩ := Finset.mem_filter.mp hT
          have hc := Finset.card_erase_add_one hvT
          have h := hr T (mem_away.mp hTW).1
          omega
        _ = (r-1)*deg v := by simp [deg,Nat.mul_comm]
    have hUnion := Finset.card_union_le (Z ∪ A) C
    have hZA := Finset.card_union_le Z A
    have hcard := Finset.card_le_card hcover
    have hErase := Finset.card_erase_add_one hv
    by_contra! hd
    have hd' : deg v ≤ d-1 := by omega
    have hm := Nat.mul_le_mul_left (r-1) hd'
    omega
  have hInc : (∑ v ∈ E, deg v) = ∑ T ∈ W, T.card := by
    calc
      (∑ v ∈ E, deg v) = ∑ v ∈ E, ∑ T ∈ W, if v ∈ T then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro v _
        exact Finset.card_filter _ _
      _ = ∑ T ∈ W, ∑ v ∈ E, if v ∈ T then 1 else 0 := Finset.sum_comm
      _ = ∑ T ∈ W, T.card := by
        apply Finset.sum_congr rfl
        intro T hT
        obtain ⟨hTB,hTp,hTq⟩ := mem_away.mp hT
        have hf : E.filter (· ∈ T) = T := by
          ext v
          constructor
          · exact fun h => (Finset.mem_filter.mp h).2
          · intro hv
            exact Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr
              ⟨fun e => hTq (e ▸ hv),Finset.mem_erase.mpr ⟨fun e => hTp (e ▸ hv),(hD.1 T hTB).1 hv⟩⟩,hv⟩
        rw [← Finset.card_filter,hf]
  have hL : (∑ _v ∈ E, d) ≤ ∑ v ∈ E, deg v := Finset.sum_le_sum hdeg
  have hU : (∑ T ∈ W, T.card) ≤ ∑ _T ∈ W, r :=
    Finset.sum_le_sum (fun T hT => hr T (mem_away.mp hT).1)
  have hh := hL.trans (hInc.le.trans hU)
  simpa [hEcard,W] using hh

#print axioms away_card_mul_lower

end FranklBlockIncidence
