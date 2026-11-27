import FranklExcludeTwelveStars

open scoped BigOperators
namespace FranklBlockIncidence
variable {α : Type*} [DecidableEq α]

/-- A thirteen-point pair-and-triple design whose triple pairs all obey
the avoidance cap has a triple incident with at least thirteen total
triple degrees. The moment proof avoids Cauchy by using 7d ≤ d² + 12. -/
theorem exists_high_triple_degree_sum_thirteen {S : Finset α} {B : Finset (Finset α)}
    (hD : PairDesign S B) (h3 : ∀ A ∈ B, A.card ≤ 3)
    (hk : S.card = 13) (hT : (triples B).Nonempty)
    (hCap : ∀ A ∈ triples B, ∀ p ∈ A, ∀ q ∈ A, p ≠ q →
      tripleDegree B p + tripleDegree B q + 27 ≤ 2*(triples B).card) :
    ∃ A ∈ triples B, 13 ≤ ∑ v ∈ A, tripleDegree B v := by
  classical
  have ht15 : 15 ≤ (triples B).card := by
    obtain ⟨A,hA⟩ := hT
    have hA3 := (Finset.mem_filter.mp hA).2
    obtain ⟨p,hp,q,hq,hne⟩ := Finset.one_lt_card.mp (show 1 < A.card by omega)
    have hp1 : 1 ≤ tripleDegree B p := Finset.card_pos.mpr ⟨A,Finset.mem_filter.mpr ⟨hA,hp⟩⟩
    have hq1 : 1 ≤ tripleDegree B q := Finset.card_pos.mpr ⟨A,Finset.mem_filter.mpr ⟨hA,hq⟩⟩
    have h := hCap A hA p hp q hq hne
    omega
  have hdv : ∀ v ∈ S, tripleDegree B v ≤ 6 := by
    intro v hv
    have h := card_containing_add_tripleDegree hD h3 hv
    have hsub : (triples B).filter (v ∈ ·) ⊆ B.filter (v ∈ ·) :=
      fun A hA => Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp (Finset.mem_filter.mp hA).1).1,
        (Finset.mem_filter.mp hA).2⟩
    have hc := Finset.card_le_card hsub
    change tripleDegree B v ≤ _ at hc
    omega
  have hnum (d : ℕ) (hd : d ≤ 6) : 7*d ≤ d^2 + 12 := by interval_cases d <;> decide
  have hLower := Finset.sum_le_sum (s := S) (fun v hv => hnum (tripleDegree B v) (hdv v hv))
  rw [← Finset.mul_sum,Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul,hk,sum_tripleDegree hD] at hLower
  have hEach (A : Finset α) (hA : A ∈ triples B) :
      2*(∑ v ∈ A, tripleDegree B v) + 81 ≤ 6*(triples B).card := by
    obtain ⟨p,q,r,hpq,hpr,hqr,hEq⟩ := Finset.card_eq_three.mp (Finset.mem_filter.mp hA).2
    have hp : p ∈ A := hEq.symm ▸ (show p ∈ ({p,q,r} : Finset α) by simp)
    have hq : q ∈ A := hEq.symm ▸ (show q ∈ ({p,q,r} : Finset α) by simp)
    have hr : r ∈ A := hEq.symm ▸ (show r ∈ ({p,q,r} : Finset α) by simp)
    have h1 := hCap A hA p hp q hq hpq
    have h2 := hCap A hA p hp r hr hpr
    have h3' := hCap A hA q hq r hr hqr
    rw [hEq]
    simp [Finset.sum_insert,hpq,hpr,hqr]
    omega
  have hUpper := Finset.sum_le_sum (s := triples B) hEach
  rw [Finset.sum_add_distrib,← Finset.mul_sum,← sum_sq_tripleDegree hD,
    Finset.sum_const,Finset.sum_const,nsmul_eq_mul,nsmul_eq_mul] at hUpper
  change 2*(∑ v ∈ S, (tripleDegree B v)^2) + (triples B).card*81 ≤
    (triples B).card*(6*(triples B).card) at hUpper
  have h18 : 18 ≤ (triples B).card := by
    by_contra! hn
    generalize he : (triples B).card = t at ht15 hn hUpper hLower
    interval_cases t <;> omega
  by_contra hn
  have h' : (∑ A ∈ triples B, ∑ v ∈ A, tripleDegree B v) ≤ ∑ _A ∈ triples B, 12 := by
    apply Finset.sum_le_sum
    intro A hA
    by_contra! ha
    exact hn ⟨A,hA,by omega⟩
  rw [← sum_sq_tripleDegree hD,Finset.sum_const,nsmul_eq_mul] at h'
  change (∑ v ∈ S, (tripleDegree B v)^2) ≤ (triples B).card * 12 at h'
  omega

#print axioms exists_high_triple_degree_sum_thirteen
end FranklBlockIncidence
