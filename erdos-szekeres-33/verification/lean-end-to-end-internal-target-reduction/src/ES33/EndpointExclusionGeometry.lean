/- Static forward proof adapted from the prior EndpointSubsets and
EndpointPolygon drafts. No compiler has run on this source. -/
import ES33.EndpointRecurrence
import ES33.AnchorReduction

namespace ES33.Endpoint

/-- Color homogeneity on all sorted triples of a selected set. -/
def MonoSet {n : ℕ} (χ : Signs n) (v : Bool) (s : Finset (Fin n)) : Prop :=
  ∀ a ∈ s, ∀ b ∈ s, ∀ c ∈ s, a < b → b < c → χ a b c = v

def BoundedSet {n : ℕ} (s : Finset (Fin n)) (a c : Fin n) : Prop :=
  a ∈ s ∧ c ∈ s ∧ ∀ b ∈ s, a ≤ b ∧ b ≤ c

/-- Recover the finite selected set from an endpoint witness. -/
theorem Ends.to_set {n d : ℕ} {χ : Signs n} (hχ : SignotopeConstraints n χ)
    {v : Bool} {a c : Fin n} (hd : 0 < d) (h : Ends χ v d a c) :
    ∃ s : Finset (Fin n), s.card = d ∧ MonoSet χ v s ∧ BoundedSet s a c := by
  obtain ⟨f,hf,ha,hc⟩ := h
  let F : Fin d → Fin n := fun i => f i
  have hF : StrictMono F := fun i j hij => hf.increasing i j hij j.isLt
  let s := Finset.univ.image F
  refine ⟨s,?_,?_,?_,?_,?_⟩
  · change (Finset.univ.image F).card = d
    rw [Finset.card_image_of_injective _ hF.injective,Finset.card_univ,Fintype.card_fin]
  · intro x hx y hy z hz hxy hyz
    rcases Finset.mem_image.mp hx with ⟨i,_,rfl⟩
    rcases Finset.mem_image.mp hy with ⟨j,_,rfl⟩
    rcases Finset.mem_image.mp hz with ⟨k,_,rfl⟩
    exact hf.all_signs hχ i j k (hF.lt_iff_lt.mp hxy) (hF.lt_iff_lt.mp hyz) k.isLt
  · exact Finset.mem_image.mpr ⟨⟨0,hd⟩,Finset.mem_univ _,ha⟩
  · exact Finset.mem_image.mpr ⟨⟨d-1,by omega⟩,Finset.mem_univ _,hc⟩
  · intro x hx
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hx
    have h₀ := hF.monotone (show (⟨0,hd⟩ : Fin d) ≤ i from Nat.zero_le _)
    have h₁ := hF.monotone (show i ≤ (⟨d-1,by omega⟩ : Fin d) from by
      change (i : ℕ) ≤ d-1
      omega)
    exact ⟨ha ▸ h₀,hc ▸ h₁⟩

private theorem packet_middle_split {a b c d : Bool} (h : EndpointPacket a b c d)
    (hm : b ≠ c) : a = b ∧ d = c := by
  cases a <;> cases b <;> cases c <;> cases d <;> simp_all [EndpointPacket]

private theorem packet_right_of_split {a b c d : Bool} (h : EndpointPacket a b c d)
    (hm : a ≠ c) : d = c := by
  cases a <;> cases b <;> cases c <;> cases d <;> simp_all [EndpointPacket]

private theorem median_of_groups_on_set {n : ℕ} {χ : Signs n}
    (hχ : SignotopeConstraints n χ) {s : Finset (Fin n)}
    {L R : Fin n} (hb : BoundedSet s L R)
    (hm : ∀ a ∈ s, ∀ b ∈ s, ∀ c ∈ s, a < b → b < c →
      (a = L ∨ χ L a R = χ L b R) →
      (c = R ∨ χ L c R = χ L b R) → χ a b c = χ L b R)
    {a b c : Fin n} (ha : a∈s) (hx : b∈s) (hc : c∈s) (hab : a<b) (hbc : b<c) :
    χ a b c = χ L b R := by
  have hL := (hb.2.2 a ha).1
  have hR := (hb.2.2 c hc).2
  have mk := fun a b c d (ha : a < b) (hb : b < c) (hc : c < d) =>
    (endpointPacket_iff _ _ _ _).mpr (hχ a b c d ha hb hc)
  have endpoint (x y : Fin n) (hx : x∈s) (hy : y∈s) (hL : L<x) (hxy : x<y) (hR : y<R) :
      χ L x y = χ L x R ∧ χ x y R = χ L y R := by
    by_cases h : χ L x R = χ L y R
    · exact ⟨hm L hb.1 x hx y hy hL hxy (Or.inl rfl) (Or.inr h.symm),
        hm x hx y hy R hb.2.1 hxy hR (Or.inr h) (Or.inl rfl)⟩
    · exact packet_middle_split (mk L x y R hL hxy hR) h
  rcases hL.eq_or_lt with rfl | hL
  · rcases hR.eq_or_lt with rfl | hR
    · rfl
    · exact (endpoint b c hx hc hab hbc hR).1
  rcases hR.eq_or_lt with rfl | hR
  · exact (endpoint a b ha hx hL hab hbc).2
  by_cases eab : χ L a R = χ L b R
  · by_cases ebc : χ L b R = χ L c R
    · exact hm a ha b hx c hc hab hbc (Or.inr eab) (Or.inr ebc.symm)
    · have eb := (endpoint a b ha hx hL hab (hbc.trans hR)).2
      have ec := (endpoint a c ha hc hL (hab.trans hbc) hR).2
      have hne : χ a b R ≠ χ a c R := by simpa only [eb,ec] using ebc
      exact (packet_middle_split (mk a b c R hab hbc hR) hne).1.trans eb
  · have ea := (endpoint a b ha hx hL hab (hbc.trans hR)).1
    have eb := (endpoint b c hx hc (hL.trans hab) hbc hR).1
    have hne : χ L a b ≠ χ L b c := by simpa only [ea,eb] using eab
    exact (packet_right_of_split (mk L a b c hL hab hbc) hne).trans eb

private theorem color_of_interior {n : ℕ} {χ : Signs n} {v : Bool}
    {s : Finset (Fin n)} {L x R : Fin n} (hb : BoundedSet s L R)
    (hm : MonoSet χ v s) (hx : x∈s) (hL : L<x) (hR : x<R) :
    χ L x R = v := hm L hb.1 x hx R hb.2.1 hL hR

/-- Opposite homogeneous chain subsets with common distinct endpoints
form an even set; they share just the endpoints. -/
theorem union_even_and_inter {n : ℕ} {χ : Signs n} (hχ : SignotopeConstraints n χ)
    {s t : Finset (Fin n)} {L R : Fin n} (hLR : L<R)
    (hs : MonoSet χ false s) (ht : MonoSet χ true t)
    (hbs : BoundedSet s L R) (hbt : BoundedSet t L R) :
    Anchor.EvenSet χ (s∪t) ∧ s∩t = {L,R} := by
  classical
  have hb : BoundedSet (s∪t) L R := by
    refine ⟨Finset.mem_union.mpr (Or.inl hbs.1),Finset.mem_union.mpr (Or.inl hbs.2.1),?_⟩
    intro x hx
    rcases Finset.mem_union.mp hx with hx|hx
    · exact hbs.2.2 x hx
    · exact hbt.2.2 x hx
  have locs (x : Fin n) (hx : x∈s∪t)
      (hc : x=L ∨ x=R ∨ χ L x R=false) : x∈s := by
    rcases hc with rfl|rfl|hc
    · exact hbs.1
    · exact hbs.2.1
    rcases Finset.mem_union.mp hx with hx|hx
    · exact hx
    have H := hbt.2.2 x hx
    rcases H.1.eq_or_lt with rfl|hL
    · exact hbs.1
    rcases H.2.eq_or_lt with rfl|hR
    · exact hbs.2.1
    have := color_of_interior hbt ht hx hL hR
    rw [this] at hc
    contradiction
  have loct (x : Fin n) (hx : x∈s∪t)
      (hc : x=L ∨ x=R ∨ χ L x R=true) : x∈t := by
    rcases hc with rfl|rfl|hc
    · exact hbt.1
    · exact hbt.2.1
    rcases Finset.mem_union.mp hx with hx|hx
    · have H := hbs.2.2 x hx
      rcases H.1.eq_or_lt with rfl|hL
      · exact hbt.1
      rcases H.2.eq_or_lt with rfl|hR
      · exact hbt.2.1
      have := color_of_interior hbs hs hx hL hR
      rw [this] at hc
      contradiction
    · exact hx
  have hmed : ∀ a∈s∪t, ∀ b∈s∪t, ∀ c∈s∪t, a<b → b<c → χ a b c=χ L b R := by
    apply fun a ha b hbb c hc hab hbc =>
      median_of_groups_on_set hχ hb ?_ ha hbb hc hab hbc
    intro a ha b hbb c hc hab hbc hA hC
    cases hcolor : χ L b R
    · exact hs a (locs a ha (hA.imp id (fun h => Or.inr (h.trans hcolor))))
        b (locs b hbb (Or.inr (Or.inr hcolor)))
        c (locs c hc (Or.inr (hC.imp id (fun h => h.trans hcolor)))) hab hbc
    · exact ht a (loct a ha (hA.imp id (fun h => Or.inr (h.trans hcolor))))
        b (loct b hbb (Or.inr (Or.inr hcolor)))
        c (loct c hc (Or.inr (hC.imp id (fun h => h.trans hcolor)))) hab hbc
  constructor
  · intro a ha b hbb c hc d hd hab hbc hcd
    rw [hmed a ha b hbb c hc hab hbc,hmed a ha b hbb d hd hab (hbc.trans hcd),
      hmed a ha c hc d hd (hab.trans hbc) hcd,hmed b hbb c hc d hd hbc hcd]
    cases χ L b R <;> cases χ L c R <;> decide
  · ext x
    constructor
    · intro hx
      obtain ⟨hsx,htx⟩ := Finset.mem_inter.mp hx
      have H := hbs.2.2 x hsx
      rcases H.1.eq_or_lt with rfl|hL
      · simp
      rcases H.2.eq_or_lt with rfl|hR
      · simp
      have e₁ := color_of_interior hbs hs hsx hL hR
      have e₂ := color_of_interior hbt ht htx hL hR
      rw [e₁] at e₂
      contradiction
    · intro hx
      simp only [Finset.mem_insert,Finset.mem_singleton] at hx
      rcases hx with rfl|rfl
      · exact Finset.mem_inter.mpr ⟨hbs.1,hbt.1⟩
      · exact Finset.mem_inter.mpr ⟨hbs.2.1,hbt.2.1⟩

/-- A common-endpoint opposite-color cap and cup define an even set of
exactly their combined size minus two. Only the needed direction is used. -/
theorem even_set_of_endpoint_pair {n k s t : ℕ} {χ : Signs n} {L R : Fin n}
    (hχ : SignotopeConstraints n χ) (hs : 2 ≤ s) (ht : 2 ≤ t)
    (hsum : s+t=k+2) (cap : Ends χ false s L R) (cup : Ends χ true t L R) :
    Anchor.HasEvenSet χ k := by
  have hLR : L<R := by
    obtain ⟨f,hf,hL,hR⟩ := cap
    rw [← hL,← hR]
    exact hf.increasing 0 (s-1) (by omega) (by omega)
  obtain ⟨S,hS,hms,hbs⟩ := cap.to_set hχ (by omega)
  obtain ⟨T,hT,hmt,hbt⟩ := cup.to_set hχ (by omega)
  obtain ⟨hE,hI⟩ := union_even_and_inter hχ hLR hms hmt hbs hbt
  have hcard₂ : ({L,R} : Finset (Fin n)).card = 2 :=
    Finset.card_pair_eq_two_iff.mpr hLR.ne
  have hc := Finset.card_union_add_card_inter S T
  rw [hI,hcard₂,hS,hT] at hc
  exact ⟨S∪T,by omega,hE⟩

/-- A positive chain provides a positive set of exactly its chain length.
The order-statistic reconstruction needed for the converse is not used. -/
theorem positive_set_of_cup {n d : ℕ} {χ : Signs n} {a c : Fin n}
    (hχ : SignotopeConstraints n χ) (hd : 0<d) (h : Ends χ true d a c) :
    Anchor.HasPositiveSet χ d := by
  obtain ⟨s,hs,hm,_⟩ := h.to_set hχ hd
  exact ⟨s,hs,hm⟩

#print axioms Ends.to_set
#print axioms union_even_and_inter
#print axioms even_set_of_endpoint_pair
#print axioms positive_set_of_cup

end ES33.Endpoint
