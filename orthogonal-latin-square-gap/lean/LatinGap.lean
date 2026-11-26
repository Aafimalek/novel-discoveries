import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Quotient
import Mathlib.Data.Fintype.Sets
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Choose
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Maximal orthogonal partial Latin squares

A filled cell is represented by four labels. Linearity says that two words
can share at most one label. Saturation says that no word can be added.
-/

namespace LatinGap
open Finset
open scoped BigOperators

/-- The four coordinates are the row, column, and two entries. -/
abbrev Coord := Fin 4

/-- A label carries its coordinate as well as its value. -/
abbrev Label (n : ℕ) := Coord × Fin n

/-- A word represents one filled cell of the superimposed pair. -/
abbrev Word (n : ℕ) := Coord → Fin n

/-- A design is a finite collection of words of the same order. -/
abbrev Design (n : ℕ) := Finset (Word n)

variable {n : ℕ} {D : Design n}

/-- No two distinct words share the same pair of labels. -/
def Linear (D : Design n) : Prop :=
  ∀ ⦃u⦄, u ∈ D → ∀ ⦃v⦄, v ∈ D → ∀ ⦃i j : Coord⦄, i ≠ j →
    u i = v i → u j = v j → u = v

/-- A label pair is used when a word contains both labels in distinct coordinates. -/
def Used (D : Design n) (x y : Label n) : Prop :=
  x.1 ≠ y.1 ∧ ∃ w ∈ D, w x.1 = x.2 ∧ w y.1 = y.2

/-- Every potential word reuses a pair and therefore cannot be inserted. -/
def Saturated (D : Design n) : Prop :=
  ∀ w : Word n, ∃ i j, Used D (i, w i) (j, w j)

/-- The words containing a specified label. -/
def incident (D : Design n) (x : Label n) : Finset (Word n) :=
  D.filter fun w => w x.1 = x.2

/-- Number of words containing a specified label. -/
def freq (D : Design n) (x : Label n) : ℕ := (incident D x).card

/-- Values in a coordinate that occur with a specified label. -/
def neighbors (D : Design n) (x : Label n) (j : Coord) : Finset (Fin n) :=
  (incident D x).image fun w => w j

/-- Used pairs are symmetric. -/
theorem used_symm {x y : Label n} : Used D x y → Used D y x := by
  rintro ⟨h, w, hw, hx, hy⟩
  exact ⟨h.symm, w, hw, hy, hx⟩

/-- A used pair always joins distinct coordinates. -/
theorem used_coord_ne {x y : Label n} (h : Used D x y) : x.1 ≠ y.1 := h.1

/-- Membership in the neighbor set expresses a used pair across coordinates. -/
theorem mem_neighbors {x : Label n} {j : Coord} {a : Fin n} (h : x.1 ≠ j) :
    a ∈ neighbors D x j ↔ Used D x (j, a) := by
  simp only [neighbors, incident, mem_image, mem_filter, Used]
  constructor
  · rintro ⟨w, ⟨hw, hx⟩, ha⟩; exact ⟨h, w, hw, hx, ha⟩
  · rintro ⟨_, w, hw, hx, ha⟩; exact ⟨w, ⟨hw, hx⟩, ha⟩

/-- Linearity makes the neighbors in any other coordinate distinct. -/
theorem card_neighbors (hD : Linear D) {x : Label n} {j : Coord} (h : x.1 ≠ j) :
    (neighbors D x j).card = freq D x := by
  apply card_image_of_injOn
  intro u hu v hv hj
  obtain ⟨huD, hux⟩ := mem_filter.mp hu
  obtain ⟨hvD, hvx⟩ := mem_filter.mp hv
  exact hD huD hvD h (hux.trans hvx.symm) hj

/-- Frequencies in each fixed coordinate sum to the number of words. -/
theorem sum_freq (D : Design n) (i : Coord) :
    ∑ a : Fin n, freq D (i, a) = D.card := by
  simp only [freq, incident, card_filter]
  rw [sum_comm]
  simp

/-- Values unused with two labels in a third coordinate. -/
def candidates (D : Design n) (x y : Label n) (j : Coord) : Finset (Fin n) :=
  univ \ (neighbors D x j ∪ neighbors D y j)

/-- A candidate forms no used pair with either of the two specified labels. -/
theorem mem_candidates {x y : Label n} {j : Coord} {a : Fin n}
    (hx : x.1 ≠ j) (hy : y.1 ≠ j) :
    a ∈ candidates D x y j ↔ ¬ Used D x (j, a) ∧ ¬ Used D y (j, a) := by
  simp [candidates, mem_neighbors hx, mem_neighbors hy, not_or]


/-- Split the total into the candidate complement and the forbidden union. -/
private theorem candidate_partition (x y : Label n) (j : Coord) :
    (candidates D x y j).card + (neighbors D x j ∪ neighbors D y j).card = n := by
  have h : (neighbors D x j ∪ neighbors D y j).card ≤ n := by
    simpa using (card_le_univ (s := neighbors D x j ∪ neighbors D y j))
  simpa [candidates, card_sdiff] using Nat.sub_add_cancel h

/-- Removing the two neighbor sets leaves at least the stated number of values. -/
theorem card_candidates_lower (hD : Linear D) {x y : Label n} {j : Coord}
    (hx : x.1 ≠ j) (hy : y.1 ≠ j) :
    n ≤ (candidates D x y j).card + freq D x + freq D y := by
  have hc := candidate_partition (D := D) x y j
  have h := card_union_le (neighbors D x j) (neighbors D y j)
  rw [card_neighbors hD hx, card_neighbors hD hy] at h
  omega

/-- A shared neighbor improves the elementary candidate bound by one. -/
theorem card_candidates_shared (hD : Linear D) {x y : Label n} {j : Coord}
    (hx : x.1 ≠ j) (hy : y.1 ≠ j) {a : Fin n}
    (hxa : Used D x (j, a)) (hya : Used D y (j, a)) :
    n + 1 ≤ (candidates D x y j).card + freq D x + freq D y := by
  have hc := candidate_partition (D := D) x y j
  have h := card_union_add_card_inter (neighbors D x j) (neighbors D y j)
  rw [card_neighbors hD hx, card_neighbors hD hy] at h
  have hi : 0 < (neighbors D x j ∩ neighbors D y j).card :=
    card_pos.mpr ⟨a, mem_inter.mpr ⟨(mem_neighbors hx).2 hxa, (mem_neighbors hy).2 hya⟩⟩
  omega

/-- In a maximal design an unused pair forces all pairs across the two
remaining candidate sets to be used. -/
theorem candidate_rectangle (hD : Saturated D)
    {x y : Label n} {j k : Coord} (hxy : x.1 ≠ y.1)
    (hxj : x.1 ≠ j) (hxk : x.1 ≠ k) (hyj : y.1 ≠ j) (hyk : y.1 ≠ k) (hjk : j ≠ k)
    (hxyU : ¬ Used D x y) {a b : Fin n}
    (ha : a ∈ candidates D x y j) (hb : b ∈ candidates D x y k) :
    Used D (j, a) (k, b) := by
  classical
  have ha' := (mem_candidates hxj hyj).1 ha
  have hb' := (mem_candidates hxk hyk).1 hb
  let w : Word n := fun i => if i = x.1 then x.2 else if i = y.1 then y.2 else
    if i = j then a else b
  have hcover (i : Coord) : i = x.1 ∨ i = y.1 ∨ i = j ∨ i = k := by
    by_contra! h
    have hsub : ({i, x.1, y.1, j, k} : Finset Coord) ⊆ univ := subset_univ _
    have hc := card_le_card hsub
    simp [h.1, h.2.1, h.2.2.1, h.2.2.2, hxy, hxj, hxk, hyj, hyk, hjk] at hc
  have wx : w x.1 = x.2 := by simp [w]
  have wy : w y.1 = y.2 := by simp [w, hxy.symm]
  have wj : w j = a := by simp [w, hxj.symm, hyj.symm]
  have wk : w k = b := by simp [w, hxk.symm, hyk.symm, hjk.symm]
  obtain ⟨i, l, hused⟩ := hD w
  rcases hcover i with rfl | rfl | rfl | rfl <;>
    rcases hcover l with rfl | rfl | rfl | rfl <;>
    simp only [wx, wy, wj, wk, Prod.mk.eta] at hused <;>
    first | exact hused | exact used_symm hused |
      exact False.elim (hused.1 rfl) |
      exact False.elim (hxyU hused) | exact False.elim (hxyU (used_symm hused)) |
      exact False.elim (ha'.1 hused) | exact False.elim (ha'.1 (used_symm hused)) |
      exact False.elim (ha'.2 hused) | exact False.elim (ha'.2 (used_symm hused)) |
      exact False.elim (hb'.1 hused) | exact False.elim (hb'.1 (used_symm hused)) |
      exact False.elim (hb'.2 hused) | exact False.elim (hb'.2 (used_symm hused))

/-- The size of a candidate set is bounded above by the frequency of any
label in the opposite set of a forced rectangle. -/
theorem card_candidates_le_freq (hD : Linear D) {x y : Label n} {j k : Coord}
    (hjk : j ≠ k) {a : Fin n} (hall : ∀ b ∈ candidates D x y k, Used D (j, a) (k, b)) :
    (candidates D x y k).card ≤ freq D (j, a) := by
  rw [← card_neighbors hD hjk]
  exact card_le_card (fun b hb => (mem_neighbors hjk).2 (hall b hb))


/-- There is a coordinate outside any set of at most three coordinates. -/
private theorem coord_outside (S : Finset Coord) (h : S.card < 4) :
    ∃ j : Coord, j ∉ S := by
  by_contra! he
  have hu : (univ : Finset Coord) ⊆ S := fun a _ => he a
  have hc := card_le_card hu
  simp at hc
  omega

/-- A coordinate contains at most as many high labels as its frequency excess. -/
theorem high_card_le {s k : ℕ} (hf : ∀ x, s ≤ freq D x)
    (hF : D.card = n * s + k) (i : Coord) :
    (univ.filter fun a : Fin n => freq D (i, a) > s).card ≤ k := by
  have hs : ∑ a : Fin n, (s + if freq D (i, a) > s then 1 else 0) ≤
      ∑ a : Fin n, freq D (i, a) := by
    apply sum_le_sum
    intro a _
    split_ifs <;> have := hf (i, a) <;> omega
  rw [sum_freq, hF, sum_add_distrib, ← card_filter] at hs
  simp only [sum_const, card_univ, Fintype.card_fin, smul_eq_mul] at hs
  omega

/-- The common-neighbor property for labels of minimum frequency. -/
theorem low_common_neighbor {s k : ℕ} (hD : Linear D) (hM : Saturated D)
    (hf : ∀ x, s ≤ freq D x) (hF : D.card = n * s + k) (hn : n = 3 * s)
    (hk : k < s) {x y z : Label n} (hxy : x.1 ≠ y.1)
    (hx : freq D x = s) (hy : freq D y = s)
    (hxz : Used D x z) (hyz : Used D y z) : Used D x y := by
  classical
  by_contra hnot
  obtain ⟨j, hj⟩ := coord_outside {x.1, y.1, z.1} (by
    simp [hxy, hxz.1, hyz.1])
  simp only [mem_insert, mem_singleton, not_or] at hj
  have hz := card_candidates_shared hD hxz.1 hyz.1 hxz hyz
  have ht := card_candidates_lower hD (Ne.symm hj.1) (Ne.symm hj.2.1)
  rw [hx, hy] at hz ht
  have hi : candidates D x y j ⊆ (univ.filter fun a : Fin n => freq D (j, a) > s) := by
    intro a ha
    have hdeg := card_candidates_le_freq hD hj.2.2 (fun b hb =>
      candidate_rectangle hM hxy (Ne.symm hj.1) hxz.1 (Ne.symm hj.2.1) hyz.1
        hj.2.2 hnot ha hb)
    exact mem_filter.mpr ⟨mem_univ _, by omega⟩
  have hh := high_card_le hf hF j
  have hl := card_le_card hi
  omega

/-- Every label has a low used neighbor in each other coordinate. -/
theorem exists_low_neighbor {s k : ℕ} (hD : Linear D) (hf : ∀ x, s ≤ freq D x)
    (hF : D.card = n * s + k) (hk : k < s) (x : Label n) (j : Coord) (h : x.1 ≠ j) :
    ∃ y : Label n, y.1 = j ∧ freq D y = s ∧ Used D x y := by
  classical
  by_contra! hno
  have hs : neighbors D x j ⊆ (univ.filter fun a : Fin n => freq D (j, a) > s) := by
    intro a ha
    have hne := hno (j, a) rfl
    have hh := (mem_neighbors h).1 ha
    have hfreq := hf (j, a)
    exact mem_filter.mpr ⟨mem_univ _, by
      by_contra! hle
      exact hne (Nat.le_antisymm hle hfreq) hh⟩
  have hcard := card_le_card hs
  rw [card_neighbors hD h] at hcard
  have hh := high_card_le hf hF j
  have hf' := hf x
  omega

/-- Two low labels in the same coordinate that share a low neighbor
have the same low neighbors. -/
theorem low_twins {s k : ℕ} (hD : Linear D) (hM : Saturated D)
    (hf : ∀ x, s ≤ freq D x) (hF : D.card = n * s + k) (hn : n = 3 * s) (hk : k < s)
    {x y z : Label n} (hxy : x.1 = y.1) (hx : freq D x = s) (hy : freq D y = s)
    (hz : freq D z = s) (hxz : Used D x z) (hyz : Used D y z)
    (v : Label n) (hv : freq D v = s) : Used D x v ↔ Used D y v := by
  classical
  have hwedge := @low_common_neighbor n D s k hD hM hf hF hn hk
  obtain ⟨j, hj⟩ := coord_outside {x.1, z.1} (by simp [hxz.1])
  simp only [mem_insert, mem_singleton, not_or] at hj
  obtain ⟨w, hwj, hw, hxw⟩ := exists_low_neighbor hD hf hF hk x j (Ne.symm hj.1)
  have hzw : Used D z w := hwedge (by rw [hwj]; exact Ne.symm hj.2) hz hw
    (used_symm hxz) (used_symm hxw)
  have hyw : Used D y w := hwedge (by rw [hwj, ← hxy]; exact Ne.symm hj.1) hy hw hyz
    (used_symm hzw)
  have step (p q : Label n) (hp : freq D p = s) (hq : freq D q = s)
      (hpq : p.1 = q.1) (hpz : Used D p z) (hqz : Used D q z)
      (hpw : Used D p w) (hqw : Used D q w) (hpv : Used D p v) : Used D q v := by
    have hqv : q.1 ≠ v.1 := hpq ▸ hpv.1
    by_cases hvz : v.1 = z.1
    · have hvw : v.1 ≠ w.1 := by rw [hvz, hwj]; exact Ne.symm hj.2
      have hwv := hwedge hvw hv hw (used_symm hpv) (used_symm hpw)
      exact hwedge hqv hq hv hqw hwv
    · have hzv := hwedge hvz hv hz (used_symm hpv) (used_symm hpz)
      exact hwedge hqv hq hv hqz hzv
  exact ⟨step x y hx hy hxy hxz hyz hxw hyw, step y x hy hx hxy.symm hyz hxz hyw hxw⟩

/-- Low labels lie in the same component if paired across coordinates,
or if they have identical low neighborhoods in the same coordinate. -/
def lowRelated (D : Design n) (s : ℕ) (x y : Label n) : Prop :=
  Used D x y ∨ (x.1 = y.1 ∧ ∀ z : Label n, freq D z = s → (Used D x z ↔ Used D y z))

/-- Across coordinates, related low labels form a used pair. -/
theorem lowRelated_used {s : ℕ} {x y : Label n} (hxy : x.1 ≠ y.1)
    (h : lowRelated D s x y) : Used D x y :=
  h.elim id (fun ht => False.elim (hxy ht.1))

/-- The relation is reflexive. -/
theorem lowRelated_refl (s : ℕ) (x : Label n) : lowRelated D s x x :=
  Or.inr ⟨rfl, fun _ _ => Iff.rfl⟩

/-- The relation is symmetric. -/
theorem lowRelated_symm {s : ℕ} {x y : Label n}
    (h : lowRelated D s x y) : lowRelated D s y x := by
  rcases h with h | ⟨hc, hn⟩
  · exact Or.inl (used_symm h)
  · exact Or.inr ⟨hc.symm, fun z hz => (hn z hz).symm⟩

/-- The common-neighbor and twin lemmas make the relation transitive on low labels. -/
theorem lowRelated_trans {s k : ℕ} (hD : Linear D) (hM : Saturated D)
    (hf : ∀ x, s ≤ freq D x) (hF : D.card = n * s + k) (hn : n = 3 * s) (hk : k < s)
    {x y z : Label n} (hx : freq D x = s) (hy : freq D y = s) (hz : freq D z = s)
    (hxy : lowRelated D s x y) (hyz : lowRelated D s y z) : lowRelated D s x z := by
  rcases hxy with xy | ⟨hc, ht⟩ <;> rcases hyz with yz | ⟨hd, hu⟩
  · by_cases h : x.1 = z.1
    · exact Or.inr ⟨h, fun v hv =>
        low_twins hD hM hf hF hn hk h hx hz hy xy (used_symm yz) v hv⟩
    · exact Or.inl (low_common_neighbor hD hM hf hF hn hk h hx hz xy (used_symm yz))
  · exact Or.inl (used_symm ((hu x hx).1 (used_symm xy)))
  · exact Or.inl ((ht z hz).2 yz)
  · exact Or.inr ⟨hc.trans hd, fun v hv => (ht v hv).trans (hu v hv)⟩


/-- Partition the labels into three blocks when every frequency is at least
\(s\) and the total excess is less than \(s\). Each block has \(s\) labels
in each coordinate, and every used pair incident to a low label stays in its block. -/
theorem three_blocks {s k : ℕ} (hD : Linear D) (hM : Saturated D)
    (hf : ∀ x, s ≤ freq D x) (hF : D.card = n * s + k) (hn : n = 3 * s) (hk : k < s) :
    ∃ block : Label n → Fin 3,
      (∀ (i : Coord) (b : Fin 3), (univ.filter fun a : Fin n => block (i, a) = b).card = s) ∧
      (∀ {x y : Label n}, freq D x = s → Used D x y → block x = block y) := by
  classical
  let L := {x : Label n // freq D x = s}
  let lowSetoid : Setoid L :=
    ⟨fun x y => lowRelated D s x.val y.val,
      fun x => lowRelated_refl s x.val,
      fun h => lowRelated_symm h,
      by
        intro x y z h h'
        exact lowRelated_trans hD hM hf hF hn hk x.property y.property z.property h h'⟩
  let Q := Quotient lowSetoid
  let _ : Fintype Q := Fintype.ofFinite Q
  let cls : L → Q := Quotient.mk lowSetoid
  have hcls {u v : L} : cls u = cls v ↔ lowRelated D s u.val v.val :=
    ⟨@Quotient.exact L lowSetoid u v, @Quotient.sound L lowSetoid u v⟩
  have cl_rep (b : Q) : ∃ u : L, cls u = b := Quotient.exists_rep b
  have some_low (x : Label n) : ∃ u : L, Used D x u.val := by
    obtain ⟨i, hi⟩ := coord_outside {x.1} (by simp)
    have hxi : x.1 ≠ i := by simpa [ne_comm] using hi
    obtain ⟨u, _, hu, hxu⟩ := exists_low_neighbor hD hf hF hk x i hxi
    exact ⟨⟨u, hu⟩, hxu⟩
  let rep (x : Label n) : L :=
    if h : freq D x = s then ⟨x, h⟩ else Classical.choose (some_low x)
  let block (x : Label n) : Q := cls (rep x)
  have block_low (x : Label n) (hx : freq D x = s) : block x = cls ⟨x, hx⟩ := by
    simp [block, rep, hx]
  have attached {x y : Label n} (hy : freq D y = s) (hxy : Used D x y) :
      block x = block y := by
    rw [block_low y hy]
    by_cases hx : freq D x = s
    · rw [block_low x hx]
      exact hcls.mpr (Or.inl hxy)
    have hrep : Used D x (rep x).val := by
      simpa [rep, hx] using Classical.choose_spec (some_low x)
    change cls (rep x) = cls ⟨y, hy⟩
    apply hcls.mpr
    by_cases h : (rep x).val.1 = y.1
    · obtain ⟨i, hi⟩ := coord_outside {x.1, y.1} (by simp [hxy.1])
      simp only [mem_insert, mem_singleton, not_or] at hi
      obtain ⟨z, hzi, hz, hxz⟩ := exists_low_neighbor hD hf hF hk x i (Ne.symm hi.1)
      have hyz : y.1 ≠ z.1 := by rw [hzi]; exact Ne.symm hi.2
      have ur := low_common_neighbor hD hM hf hF hn hk (h ▸ hyz)
        (rep x).property hz (used_symm hrep) (used_symm hxz)
      have vr := low_common_neighbor hD hM hf hF hn hk hyz hy hz
        (used_symm hxy) (used_symm hxz)
      exact lowRelated_trans hD hM hf hF hn hk (rep x).property hz hy
        (Or.inl ur) (Or.inl (used_symm vr))
    · exact Or.inl (low_common_neighbor hD hM hf hF hn hk h (rep x).property hy
        (used_symm hrep) (used_symm hxy))
  have occupied (b : Q) (i : Coord) :
      ∃ x : Label n, x.1 = i ∧ freq D x = s ∧ block x = b := by
    obtain ⟨v, hv⟩ := cl_rep b
    by_cases h : v.val.1 = i
    · exact ⟨v.val, h, v.property, (block_low _ v.property).trans hv⟩
    obtain ⟨x, hxi, hx, hvx⟩ := exists_low_neighbor hD hf hF hk v.val i h
    exact ⟨x, hxi, hx, (attached hx hvx).symm.trans ((block_low _ v.property).trans hv)⟩
  let fiber (i : Coord) (b : Q) : Finset (Fin n) := univ.filter fun a => block (i, a) = b
  let lowFiber (i : Coord) (b : Q) : Finset (Fin n) :=
    (fiber i b).filter fun a => freq D (i, a) = s
  have hbsize (i : Coord) (b : Q) : s ≤ (fiber i b).card ∧ (lowFiber i b).card ≤ s := by
    obtain ⟨j, hj⟩ := coord_outside {i} (by simp)
    have hji : j ≠ i := by simpa using hj
    obtain ⟨x, hxj, hx, hxb⟩ := occupied b j
    have hxi : x.1 ≠ i := hxj ▸ hji
    have hnsub : neighbors D x i ⊆ fiber i b := by
      intro a ha
      have hpair := (mem_neighbors hxi).1 ha
      exact mem_filter.mpr ⟨mem_univ _, (attached hx (used_symm hpair)).trans hxb⟩
    have hlsub : lowFiber i b ⊆ neighbors D x i := by
      intro a ha
      obtain ⟨hab, hf'a⟩ := mem_filter.mp ha
      have hb'a := (mem_filter.mp hab).2
      have he : cls ⟨x, hx⟩ = cls ⟨(i, a), hf'a⟩ := by
        rw [← block_low x hx, ← block_low (i, a) hf'a, hb'a, hxb]
      exact (mem_neighbors hxi).2 (lowRelated_used hxi (hcls.mp he))
    have hcard := card_neighbors hD hxi
    rw [hx] at hcard
    exact ⟨hcard ▸ card_le_card hnsub, hcard ▸ card_le_card hlsub⟩
  have hsum (i : Coord) : ∑ b : Q, (fiber i b).card = n := by
    simp only [fiber, card_filter]
    rw [sum_comm]
    simp
  have hsum_low (i : Coord) :
      ∑ b : Q, (lowFiber i b).card = (univ.filter fun a : Fin n => freq D (i, a) = s).card := by
    simpa only [lowFiber, fiber, filter_filter, and_comm, mem_univ, true_and, filter_true] using
      sum_card_fiberwise_eq_card_filter
        (univ.filter fun a : Fin n => freq D (i, a) = s)
        (univ : Finset Q) (fun a => block (i, a))
  have hs_pos : 0 < s := by omega
  have upper : Fintype.card Q ≤ 3 := by
    have h := sum_le_sum (s := (univ : Finset Q)) (fun b _ => (hbsize 0 b).1)
    rw [hsum] at h
    simp only [sum_const, card_univ, smul_eq_mul] at h
    rw [hn, mul_comm 3 s, mul_comm (Fintype.card Q) s] at h
    exact Nat.le_of_mul_le_mul_left h hs_pos
  have lower : 3 ≤ Fintype.card Q := by
    have hh := high_card_le hf hF 0
    have hlow :
        (univ.filter fun a : Fin n => freq D (0, a) = s) =
          univ \ (univ.filter fun a : Fin n => freq D (0, a) > s) := by
      ext a; simp only [mem_sdiff, mem_filter, mem_univ, true_and, not_lt]
      exact ⟨fun h => h.le, fun h => h.antisymm (hf (0, a))⟩
    have hb := sum_le_sum (s := (univ : Finset Q)) (fun b _ => (hbsize 0 b).2)
    rw [hsum_low, hlow] at hb
    rw [card_sdiff_of_subset (subset_univ _)] at hb
    simp only [card_univ, Fintype.card_fin, sum_const, smul_eq_mul] at hb
    by_contra! h
    have hs2 := Nat.mul_le_mul_right s (show Fintype.card Q ≤ 2 by omega)
    omega
  have hQ : Fintype.card Q = 3 := lower.antisymm' upper
  have hexact (i : Coord) (b : Q) : (fiber i b).card = s := by
    refine le_antisymm ?_ (hbsize i b).1
    by_contra! h
    have hsum_lt := sum_lt_sum (s := (univ : Finset Q))
      (fun a _ => (hbsize i a).1) ⟨b, mem_univ _, h⟩
    rw [hsum, hn] at hsum_lt
    simp [hQ] at hsum_lt
  let e : Q ≃ Fin 3 := Fintype.equivFinOfCardEq hQ
  refine ⟨e ∘ block, ?_, ?_⟩
  · intro i b
    change (univ.filter fun a : Fin n => e (block (i, a)) = b).card = s
    have hfilt : (univ.filter fun a : Fin n => e (block (i, a)) = b) = fiber i (e.symm b) := by
      ext a; simp [fiber, ← e.eq_symm_apply]
    rw [hfilt, hexact]
  · intro x y hx hxy
    exact congrArg e (attached hx (used_symm hxy)).symm


/-- Any three words over at most two values in each coordinate include
two words agreeing in two distinct coordinates. -/
private theorem small_projection_card {T : Design n} (hD : Linear D) (hT : T ⊆ D)
    (hcard : ∀ i : Coord, (T.image fun w => w i).card ≤ 2) : T.card ≤ 2 := by
  classical
  by_contra! hlarge
  obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩ := two_lt_card.mp hlarge
  have coordAgree (i : Coord) : a i = b i ∨ a i = c i ∨ b i = c i := by
    by_contra! h
    have hsub : ({a i, b i, c i} : Finset (Fin n)) ⊆ (T.image fun w => w i) := by
      intro x hx
      simp only [mem_insert, mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact mem_image_of_mem _ ha
      · exact mem_image_of_mem _ hb
      · exact mem_image_of_mem _ hc
    have ht := card_le_card hsub
    simp [h.1, h.2.1, h.2.2] at ht
    exact (hcard i).not_gt ht
  let agrees (i : Coord) (p : Fin 3) : Prop :=
    if p = 0 then a i = b i else if p = 1 then a i = c i else b i = c i
  have htag (i : Coord) : ∃ p, agrees i p := by
    rcases coordAgree i with h | h | h
    · exact ⟨0, by simpa [agrees] using h⟩
    · exact ⟨1, by simpa [agrees] using h⟩
    · exact ⟨2, by simpa [agrees] using h⟩
  choose tag htag using htag
  obtain ⟨i, j, hij, hsame⟩ := Fintype.exists_ne_map_eq_of_card_lt tag (by decide)
  have hi := htag i
  have hj := htag j
  rw [← hsame] at hj
  generalize hp : tag i = p at hi hj
  fin_cases p <;> simp [agrees] at hi hj
  · exact hab (hD (hT ha) (hT hb) hij hi hj)
  · exact hac (hD (hT ha) (hT hc) hij hi hj)
  · exact hbc (hD (hT hb) (hT hc) hij hi hj)

/-- If every label has frequency at least \(s\), neither of the next two
sizes above \(3s^2\) can occur when the excess is less than \(s\). -/
theorem exclude_with_minimum {s k : ℕ} (hD : Linear D) (hM : Saturated D)
    (hf : ∀ x, s ≤ freq D x) (hF : D.card = n * s + k) (hn : n = 3 * s)
    (hk : k < s) (hp : 0 < k) (ht : k ≤ 2) : False := by
  classical
  obtain ⟨block, hbsize, hstay⟩ := three_blocks hD hM hf hF hn hk
  let inside (w : Word n) : Prop := ∀ i j : Coord, block (i, w i) = block (j, w j)
  let I := D.filter inside
  let C := D.filter fun w => ¬ inside w
  have hIC : I.card + C.card = D.card := by
    exact card_filter_add_card_filter_not (s := D) inside
  have pairLimit (i j : Coord) (hij : i ≠ j) (T : Design n) (hTD : T ⊆ D)
      (hinside : ∀ w ∈ T, block (i, w i) = block (j, w j)) : T.card ≤ n * s := by
    let P : Finset (Fin n × Fin n) := univ.filter fun p => block (i, p.1) = block (j, p.2)
    have hP : P.card = n * s := by
      simp only [P, card_filter, ← univ_product_univ, sum_product]
      calc
        _ = ∑ a : Fin n, (univ.filter fun b : Fin n => block (j, b) = block (i, a)).card := by
          apply sum_congr rfl
          intro a _
          rw [card_filter]
          apply sum_congr rfl
          intro b _
          congr 1
          exact propext eq_comm
        _ = _ := by simp [hbsize]
    rw [← hP]
    apply card_le_card_of_injOn (fun w : Word n => (w i, w j))
    · intro w hw
      exact mem_filter.mpr ⟨mem_univ _, hinside w hw⟩
    · intro u hu v hv huv
      exact hD (hTD hu) (hTD hv) hij (congrArg Prod.fst huv) (congrArg Prod.snd huv)
  have cNonempty : C.Nonempty := by
    by_contra! he
    have hI := pairLimit 0 1 (by decide) I (filter_subset _ _) fun w hw =>
      (mem_filter.mp hw).2 0 1
    have h0 : C.card = 0 := card_eq_zero.mpr he
    omega
  obtain ⟨w, hw⟩ := cNonempty
  have hw' : w ∈ D ∧ ¬ inside w := mem_filter.mp hw
  obtain ⟨i, j, hij, hwblock⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt (fun i : Coord => block (i, w i)) (by decide)
  have hnotI : w ∉ I := fun h => hw'.2 (mem_filter.mp h).2
  have hlim := pairLimit i j hij (insert w I)
    (by intro x hx; rcases mem_insert.mp hx with rfl | hx; exact hw'.1; exact (mem_filter.mp hx).1)
    (by
      intro x hx
      rcases mem_insert.mp hx with rfl | hx
      · exact hwblock
      · exact (mem_filter.mp hx).2 i j)
  rw [card_insert_of_notMem hnotI] at hlim
  have high_cross (u : Word n) (hu : u ∈ C) (l : Coord) : s < freq D (l, u l) := by
    have ⟨huD, huC⟩ := mem_filter.mp hu
    apply lt_of_le_of_ne (hf (l, u l))
    intro he
    apply huC
    have at_l (j : Coord) : block (l, u l) = block (j, u j) := by
      by_cases hlj : l = j
      · simp [hlj]
      · exact hstay he.symm ⟨hlj, u, huD, rfl, rfl⟩
    intro i j
    exact (at_l i).symm.trans (at_l j)
  have image_bound (i : Coord) : (C.image fun u => u i).card ≤ k := by
    apply (card_le_card ?_).trans (high_card_le hf hF i)
    intro a ha
    obtain ⟨u, hu, rfl⟩ := mem_image.mp ha
    exact mem_filter.mpr ⟨mem_univ _, high_cross u hu i⟩
  have hC : C.card ≤ k := by
    by_cases hk1 : k = 1
    · subst k
      apply card_le_one.mpr
      intro u hu v hv
      have agree (i : Coord) : u i = v i :=
        card_le_one.mp (image_bound i) _ (mem_image_of_mem _ hu) _ (mem_image_of_mem _ hv)
      exact funext agree
    · have hk2 : k = 2 := by omega
      subst k
      exact small_projection_card hD (filter_subset _ _) image_bound
  omega


/-- The values in a coordinate that do not occur with a fixed label. -/
def unused (D : Design n) (x : Label n) (i : Coord) : Finset (Fin n) :=
  univ \ neighbors D x i

/-- A value belongs to the complement exactly when its pair is unused. -/
theorem mem_unused {x : Label n} {i : Coord} {a : Fin n} (h : x.1 ≠ i) :
    a ∈ unused D x i ↔ ¬Used D x (i, a) := by
  simp [unused, mem_neighbors h]

/-- The complement in another coordinate has \(n-f(x)\) values. -/
theorem card_unused (hD : Linear D) {x : Label n} {i : Coord} (h : x.1 ≠ i) :
    (unused D x i).card = n - freq D x := by
  simp [unused, card_sdiff, card_neighbors hD h]

/-- A matching of unused pairs between two specified pools of values. -/
private def Matching (D : Design n) (i j : Coord) (U V : Finset (Fin n))
    (T : Finset (Fin n × Fin n)) : Prop :=
  (∀ p ∈ T, p.1 ∈ U ∧ p.2 ∈ V ∧ ¬Used D (i, p.1) (j, p.2)) ∧
  Set.InjOn Prod.fst (↑T : Set (Fin n × Fin n)) ∧ Set.InjOn Prod.snd (↑T : Set (Fin n × Fin n))

/-- An injective projection stays injective when an unused value is inserted. -/
private theorem injOn_insert_fresh {α β : Type*} [DecidableEq α] [DecidableEq β]
    {f : α → β} {S : Finset α} {p : α}
    (hf : Set.InjOn f ↑S) (hp : f p ∉ S.image f) :
    Set.InjOn f (↑(insert p S) : Set α) := by
  intro a ha b hb he
  change a ∈ insert p S at ha
  change b ∈ insert p S at hb
  rcases mem_insert.mp ha with rfl | haS
  · rcases mem_insert.mp hb with rfl | hbS
    · rfl
    · exact (hp (he.symm ▸ mem_image_of_mem f hbS)).elim
  · rcases mem_insert.mp hb with rfl | hbS
    · exact (hp (he ▸ mem_image_of_mem f haS)).elim
    · exact hf haS hbS he

/-- A pair of unmatched endpoints can be appended to a matching. -/
private theorem matching_insert {i j : Coord} {U V : Finset (Fin n)}
    {T : Finset (Fin n × Fin n)} {p : Fin n × Fin n}
    (hT : Matching D i j U V T) (hu : p.1 ∈ U) (hv : p.2 ∈ V)
    (hp : ¬Used D (i, p.1) (j, p.2))
    (hfix : p.1 ∉ T.image Prod.fst) (hsix : p.2 ∉ T.image Prod.snd) :
    Matching D i j U V (insert p T) := by
  refine ⟨?_, injOn_insert_fresh hT.2.1 hfix, injOn_insert_fresh hT.2.2 hsix⟩
  intro r hr
  rcases mem_insert.mp hr with rfl | hr
  · exact ⟨hu, hv, hp⟩
  · exact hT.1 r hr

/-- Removing an edge from a matching preserves the matching. -/
private theorem matching_erase {i j : Coord} {U V : Finset (Fin n)}
    {T : Finset (Fin n × Fin n)} {p : Fin n × Fin n} (hT : Matching D i j U V T) :
    Matching D i j U V (T.erase p) :=
  ⟨fun r hr => hT.1 r (erase_subset p T hr),
    hT.2.1.mono (by simp),
    hT.2.2.mono (by simp)⟩

/-- There is a matching whose cardinality dominates every other matching. -/
private theorem exists_max_matching (i j : Coord) (U V : Finset (Fin n)) :
    ∃ T : Finset (Fin n × Fin n), Matching D i j U V T ∧
      ∀ R : Finset (Fin n × Fin n), Matching D i j U V R → R.card ≤ T.card := by
  classical
  let pool := (univ : Finset (Fin n × Fin n)).powerset.filter (Matching D i j U V)
  have he : ∅ ∈ pool := by
    simp [pool, Matching, Set.InjOn]
  obtain ⟨T, hT, hmax⟩ := exists_max_image pool card ⟨∅, he⟩
  exact ⟨T, (mem_filter.mp hT).2, fun R hR => hmax R (by simp [pool, hR])⟩

/-- Unmatched values across a maximum matching always form a used pair. -/
private theorem unmatched_used {i j : Coord} {U V : Finset (Fin n)}
    {T : Finset (Fin n × Fin n)} (hT : Matching D i j U V T)
    (hmax : ∀ R, Matching D i j U V R → R.card ≤ T.card)
    {a b : Fin n} (ha : a ∈ U \ T.image Prod.fst) (hb : b ∈ V \ T.image Prod.snd) :
    Used D (i, a) (j, b) := by
  classical
  by_contra hnot
  obtain ⟨haU, haT⟩ := mem_sdiff.mp ha
  obtain ⟨hbV, hbT⟩ := mem_sdiff.mp hb
  have h := hmax _ (matching_insert (p := (a, b)) hT haU hbV hnot haT hbT)
  have hp : (a, b) ∉ T := fun hp => haT (mem_image_of_mem _ hp)
  rw [card_insert_of_notMem hp] at h
  omega

/-- An unmatched pair and a matching edge cannot be the ends of a
length-three augmenting path of unused pairs. -/
private theorem unmatched_augment {i j : Coord} {U V : Finset (Fin n)}
    {T : Finset (Fin n × Fin n)} (hT : Matching D i j U V T)
    (hmax : ∀ R, Matching D i j U V R → R.card ≤ T.card)
    {a b : Fin n} (ha : a ∈ U \ T.image Prod.fst) (hb : b ∈ V \ T.image Prod.snd)
    {p : Fin n × Fin n} (hp : p ∈ T) :
    Used D (i, a) (j, p.2) ∨ Used D (i, p.1) (j, b) := by
  classical
  by_contra! hnot
  obtain ⟨haU, haT⟩ := mem_sdiff.mp ha
  obtain ⟨hbV, hbT⟩ := mem_sdiff.mp hb
  have both := hT.1 p hp
  let rest := T.erase p
  have hrest := matching_erase (p := p) hT
  have not_fst : p.1 ∉ rest.image Prod.fst := by
    intro he
    obtain ⟨r, hr, he⟩ := mem_image.mp he
    exact (mem_erase.mp hr).1 (hT.2.1 (erase_subset _ _ hr) hp he)
  have not_snd : p.2 ∉ rest.image Prod.snd := by
    intro he
    obtain ⟨r, hr, he⟩ := mem_image.mp he
    exact (mem_erase.mp hr).1 (hT.2.2 (erase_subset _ _ hr) hp he)
  have ba : b ∉ rest.image Prod.snd := fun h => hbT (image_subset_image (erase_subset _ _) h)
  have ab : a ∉ rest.image Prod.fst := fun h => haT (image_subset_image (erase_subset _ _) h)
  have hadd := matching_insert (p := (a, p.2)) hrest haU both.2.1 hnot.1 ab not_snd
  have ha_ne : p.1 ≠ a := fun h => haT (h ▸ mem_image_of_mem _ hp)
  have hb_ne : b ≠ p.2 := fun h => hbT (h.symm ▸ mem_image_of_mem _ hp)
  have hmore := matching_insert (p := (p.1, b)) hadd both.1 hbV hnot.2
    (by intro h; rw [image_insert, mem_insert] at h; exact h.elim ha_ne not_fst)
    (by intro h; rw [image_insert, mem_insert] at h; exact h.elim hb_ne ba)
  have hc := hmax _ hmore
  have hpa : (a, p.2) ∉ rest := fun h => ab (mem_image_of_mem _ h)
  have hpb : (p.1, b) ∉ insert (a, p.2) rest := by
    intro he
    rcases mem_insert.mp he with he | he
    · exact ha_ne (congrArg Prod.fst he)
    · exact ba (mem_image_of_mem _ he)
  rw [card_insert_of_notMem hpb, card_insert_of_notMem hpa] at hc
  change (T.erase p).card + 1 + 1 ≤ T.card at hc
  have horig := card_erase_add_one hp
  omega

/-- Each matched edge forces every label unused with the fixed label in
the fourth coordinate to occur with one or both of its two endpoints. -/
private theorem matched_covers (hM : Saturated D) {x : Label n} {i j k : Coord}
    (hi : x.1 ≠ i) (hj : x.1 ≠ j) (hk : x.1 ≠ k)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    {a b c : Fin n} (ha : a ∈ unused D x i) (hb : b ∈ unused D x j)
    (hc : c ∈ unused D x k) (hab : ¬Used D (i, a) (j, b)) :
    Used D (i, a) (k, c) ∨ Used D (j, b) (k, c) := by
  by_cases h : Used D (i, a) (k, c)
  · exact Or.inl h
  · exact Or.inr (candidate_rectangle hM hi hj hk hij hik hjk
      ((mem_unused hi).1 ha)
      ((mem_candidates hj hij).2 ⟨(mem_unused hj).1 hb, hab⟩)
      ((mem_candidates hk hik).2 ⟨(mem_unused hk).1 hc, h⟩))


/-- The unmatched endpoints force enough used neighbors in their opposite
coordinates, by counting the matching edges that cannot be augmented. -/
private theorem unmatched_freq_sum (hD : Linear D) {i j : Coord} (hij : i ≠ j)
    {U V : Finset (Fin n)} {T : Finset (Fin n × Fin n)}
    (hT : Matching D i j U V T)
    (hmax : ∀ R, Matching D i j U V R → R.card ≤ T.card)
    {a b : Fin n} (ha : a ∈ U \ T.image Prod.fst) (hb : b ∈ V \ T.image Prod.snd) :
    (U \ T.image Prod.fst).card + (V \ T.image Prod.snd).card + T.card ≤
      freq D (i, a) + freq D (j, b) := by
  classical
  let L := T.filter fun p => Used D (i, p.1) (j, b)
  let R := T.filter fun p => Used D (i, a) (j, p.2)
  have hL : L ⊆ T := filter_subset _ _
  have hR : R ⊆ T := filter_subset _ _
  have hcover : T = L ∪ R := by
    apply le_antisymm _ (union_subset hL hR)
    intro p hp
    rcases unmatched_augment hT hmax ha hb hp with h | h
    · exact mem_union.mpr (Or.inr (mem_filter.mpr ⟨hp, h⟩))
    · exact mem_union.mpr (Or.inl (mem_filter.mpr ⟨hp, h⟩))
  have hcard : T.card ≤ L.card + R.card := by
    rw [hcover]
    exact card_union_le _ _
  have hleft : (U \ T.image Prod.fst).card + L.card ≤ freq D (j, b) := by
    have hd : Disjoint (U \ T.image Prod.fst) (L.image Prod.fst) := by
      rw [Finset.disjoint_left]
      intro a ha' he
      exact (mem_sdiff.mp ha').2 (image_subset_image hL he)
    rw [← card_image_of_injOn (hT.2.1.mono (by simpa using hL)), ← card_union_of_disjoint hd,
      ← card_neighbors hD hij.symm]
    apply card_le_card
    intro a h
    rcases mem_union.mp h with h | h
    · exact (mem_neighbors hij.symm).2 (used_symm (unmatched_used hT hmax h hb))
    · obtain ⟨p, hp, rfl⟩ := mem_image.mp h
      exact (mem_neighbors hij.symm).2 (used_symm (mem_filter.mp hp).2)
  have hright : (V \ T.image Prod.snd).card + R.card ≤ freq D (i, a) := by
    have hd : Disjoint (V \ T.image Prod.snd) (R.image Prod.snd) := by
      rw [Finset.disjoint_left]
      intro b hb' he
      exact (mem_sdiff.mp hb').2 (image_subset_image hR he)
    rw [← card_image_of_injOn (hT.2.2.mono (by simpa using hR)), ← card_union_of_disjoint hd,
      ← card_neighbors hD hij]
    apply card_le_card
    intro b h
    rcases mem_union.mp h with h | h
    · exact (mem_neighbors hij).2 (unmatched_used hT hmax ha h)
    · obtain ⟨p, hp, rfl⟩ := mem_image.mp h
      exact (mem_neighbors hij).2 (mem_filter.mp hp).2
  omega

/-- Sum a pointwise bound over an arbitrary pairing of two equal-size sets. -/
private theorem sum_two_pools {A B : Finset (Fin n)} {f g : Fin n → ℕ} {a : ℕ}
    (hcard : A.card = B.card) (h : ∀ x ∈ A, ∀ y ∈ B, a ≤ f x + g y) :
    A.card * a ≤ (∑ x ∈ A, f x) + (∑ y ∈ B, g y) := by
  classical
  let e : A ≃ B := Fintype.equivOfCardEq (by simpa using hcard)
  have hsum : (∑ x : A, a) ≤ ∑ x : A, (f x + g (e x)) := by
    apply sum_le_sum
    intro x _
    exact h x x.property (e x) (e x).property
  rw [sum_add_distrib] at hsum
  have he : (∑ x : A, g (e x)) = ∑ y : B, g y := Fintype.sum_equiv e _ _ (fun _ => rfl)
  rw [he, Finset.univ_eq_attach A, Finset.univ_eq_attach B, sum_attach, sum_attach] at hsum
  simpa [sum_const, smul_eq_mul] using hsum

/-- The frequencies in a coordinate split between the neighbors of a label,
the matched values outside its neighborhood, and the unmatched values. -/
private theorem sum_split {x : Label n} {i : Coord} {M : Finset (Fin n)}
    (hM : M ⊆ unused D x i) :
    (∑ a ∈ neighbors D x i, freq D (i, a)) +
      (∑ a ∈ M, freq D (i, a)) +
      (∑ a ∈ unused D x i \ M, freq D (i, a)) = D.card := by
  classical
  have h1 := sum_sdiff (f := fun a => freq D (i, a)) hM
  have h2 := sum_sdiff (f := fun a => freq D (i, a))
    (subset_univ (neighbors D x i))
  rw [sum_freq] at h2
  change (∑ a ∈ unused D x i, freq D (i, a)) +
    (∑ a ∈ neighbors D x i, freq D (i, a)) = D.card at h2
  omega

/-- The matching-count inequality for a minimum-frequency label. The
two extra conclusions record what happens at a perfect matching and at
equality in the inequality, respectively. -/
theorem matching_frequency_bound (hD : Linear D) (hM : Saturated D)
    {m : ℕ} {x : Label n} (hx : freq D x = m) (hmin : ∀ y, m ≤ freq D y)
    {i j k : Coord} (hi : x.1 ≠ i) (hj : x.1 ≠ j) (hk : x.1 ≠ k)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    let q := n - m
    ∃ t ≤ q, 2 * D.card ≥ 2 * m ^ 2 + q ^ 2 + (q-t) ^ 2 ∧
      (t = q → ∀ c ∈ unused D x k, q ≤ 2 * freq D (k, c)) ∧
      (2 * D.card = 2 * m ^ 2 + q ^ 2 + (q-t) ^ 2 →
        ∀ a ∈ neighbors D x i, freq D (i, a) = m) := by
  classical
  dsimp
  let q := n - m
  let U := unused D x i
  let V := unused D x j
  let W := unused D x k
  have cU : U.card = q := by simp [U, q, card_unused hD hi, hx]
  have cV : V.card = q := by simp [V, q, card_unused hD hj, hx]
  have cW : W.card = q := by simp [W, q, card_unused hD hk, hx]
  obtain ⟨T, hT, hmax⟩ := exists_max_matching (D := D) i j U V
  let t := T.card
  let A := T.image Prod.fst
  let B := T.image Prod.snd
  have hAU : A ⊆ U := by
    intro a ha
    obtain ⟨p, hp, rfl⟩ := mem_image.mp ha
    exact (hT.1 p hp).1
  have hBV : B ⊆ V := by
    intro b hb
    obtain ⟨p, hp, rfl⟩ := mem_image.mp hb
    exact (hT.1 p hp).2.1
  have cA : A.card = t := card_image_of_injOn hT.2.1
  have cB : B.card = t := card_image_of_injOn hT.2.2
  have ht : t ≤ q := by simpa [cA, cU] using card_le_card hAU
  have cU' : (U \ A).card = q-t := by rw [card_sdiff_of_subset hAU, cU, cA]
  have cV' : (V \ B).card = q-t := by rw [card_sdiff_of_subset hBV, cV, cB]
  have cover {p : Fin n × Fin n} (hp : p ∈ T) {c : Fin n} (hc : c ∈ W) :
      Used D (i, p.1) (k, c) ∨ Used D (j, p.2) (k, c) := by
    obtain ⟨ha, hb, hab⟩ := hT.1 p hp
    exact matched_covers hM hi hj hk hij hik hjk ha hb hc hab
  have sum_matched : t*q ≤
      (∑ a ∈ A, freq D (i, a)) + (∑ b ∈ B, freq D (j, b)) := by
    rw [show (∑ a ∈ A, freq D (i, a)) = ∑ p ∈ T, freq D (i, p.1) by
      exact sum_image hT.2.1]
    rw [show (∑ b ∈ B, freq D (j, b)) = ∑ p ∈ T, freq D (j, p.2) by
      exact sum_image hT.2.2]
    rw [← sum_add_distrib, ← show (∑ _ ∈ T, q) = t*q by simp [t]]
    apply sum_le_sum
    intro p hp
    have hsub : W ⊆ neighbors D (i, p.1) k ∪ neighbors D (j, p.2) k := by
      intro c hc
      exact mem_union.mpr ((cover hp hc).imp (mem_neighbors hik).2 (mem_neighbors hjk).2)
    rw [← cW, ← card_neighbors hD hik, ← card_neighbors hD hjk]
    exact (card_le_card hsub).trans (card_union_le _ _)
  have sum_unmatched : (q-t)*(q+(q-t)) ≤
      (∑ a ∈ U \ A, freq D (i, a)) + (∑ b ∈ V \ B, freq D (j, b)) := by
    rw [← cU']
    apply sum_two_pools (cU'.trans cV'.symm)
    intro a ha b hb
    have hh := unmatched_freq_sum hD hij hT hmax ha hb
    rw [cU', cV'] at hh
    omega
  have excl (l : Coord) (hl : x.1 ≠ l) :
      m*m ≤ ∑ a ∈ neighbors D x l, freq D (l, a) := by
    have hh := sum_le_sum (s := neighbors D x l) (fun a _ => hmin (l, a))
    simpa [sum_const, smul_eq_mul, card_neighbors hD hl, hx] using hh
  have excA := excl i hi
  have excB := excl j hj
  have splitA := sum_split (x := x) hAU
  have splitB := sum_split (x := x) hBV
  change (∑ a ∈ neighbors D x i, freq D (i, a)) +
    (∑ a ∈ A, freq D (i, a)) + (∑ a ∈ U \ A, freq D (i, a)) = D.card at splitA
  change (∑ a ∈ neighbors D x j, freq D (j, a)) +
    (∑ a ∈ B, freq D (j, a)) + (∑ a ∈ V \ B, freq D (j, a)) = D.card at splitB
  have score : 2 * m ^ 2 + q ^ 2 + (q-t) ^ 2 =
      m*m + m*m + t*q + (q-t)*(q+(q-t)) := by
    have hsum := Nat.sub_add_cancel ht
    nlinarith
  refine ⟨t, ht, ?_, ?_, ?_⟩
  · rw [score]
    omega
  · intro hperfect c hc
    let L := T.filter fun p => Used D (i, p.1) (k, c)
    let R := T.filter fun p => Used D (j, p.2) (k, c)
    have hL : L ⊆ T := filter_subset _ _
    have hR : R ⊆ T := filter_subset _ _
    have hcover : T = L ∪ R := by
      apply le_antisymm _ (union_subset hL hR)
      intro p hp
      exact mem_union.mpr ((cover hp hc).imp (fun h => mem_filter.mpr ⟨hp, h⟩)
        (fun h => mem_filter.mpr ⟨hp, h⟩))
    have hl : L.card ≤ freq D (k, c) := by
      rw [← card_image_of_injOn (hT.2.1.mono (by simpa using hL)),
        ← card_neighbors hD hik.symm]
      apply card_le_card
      intro a ha
      obtain ⟨p, hp, rfl⟩ := mem_image.mp ha
      exact (mem_neighbors hik.symm).2 (used_symm (mem_filter.mp hp).2)
    have hr : R.card ≤ freq D (k, c) := by
      rw [← card_image_of_injOn (hT.2.2.mono (by simpa using hR)),
        ← card_neighbors hD hjk.symm]
      apply card_le_card
      intro a ha
      obtain ⟨p, hp, rfl⟩ := mem_image.mp ha
      exact (mem_neighbors hjk.symm).2 (used_symm (mem_filter.mp hp).2)
    have htt : t ≤ L.card + R.card := by
      change T.card ≤ L.card + R.card
      rw [hcover]
      exact card_union_le _ _
    omega
  · intro he a ha
    rw [score] at he
    apply le_antisymm _ (hmin (i, a))
    by_contra hab
    have hstrict : m*m < ∑ b ∈ neighbors D x i, freq D (i, b) := by
      have hh := sum_lt_sum (s := neighbors D x i)
        (fun b _ => hmin (i, b)) ⟨a, ha, Nat.lt_of_not_ge hab⟩
      simpa [sum_const, smul_eq_mul, card_neighbors hD hi, hx] using hh
    omega


/-- Choose the other two coordinates after one distinct coordinate has
already been specified. -/
private theorem other_coordinates (x i : Coord) (hi : x ≠ i) :
    ∃ j k : Coord, x ≠ j ∧ x ≠ k ∧ i ≠ j ∧ i ≠ k ∧ j ≠ k := by
  obtain ⟨j, hj⟩ := coord_outside {x, i} (by simp [hi])
  simp only [mem_insert, mem_singleton, not_or] at hj
  obtain ⟨k, hk⟩ := coord_outside {x, i, j} (by simp [hi, Ne.symm hj.1, Ne.symm hj.2])
  simp only [mem_insert, mem_singleton, not_or] at hk
  exact ⟨j, k, Ne.symm hj.1, Ne.symm hk.1, Ne.symm hj.2, Ne.symm hk.2.1, Ne.symm hk.2.2⟩

/-- For the first two sizes above the bound, the matching inequality
constrains the deficit of the minimum from \(s\). -/
private theorem minimum_deficit {s k : ℕ} (hD : Linear D) (hM : Saturated D)
    (hs : 2 ≤ s) (hn : n = 3*s) (hk : k ≤ 2) (hF : D.card = n*s+k) :
    ∃ x : Label n, (∀ y, freq D x ≤ freq D y) ∧
      freq D x ≤ s ∧ 3 * (s-freq D x)^2 ≤ 2*k := by
  classical
  have hnpos : 0 < n := by omega
  let initial : Label n := (0, ⟨0, hnpos⟩)
  obtain ⟨x, _, hmin'⟩ := exists_min_image (univ : Finset (Label n)) (freq D)
    ⟨initial, mem_univ _⟩
  have hmin (y : Label n) := hmin' y (mem_univ _)
  let m := freq D x
  have hlow : m ≤ s := by
    have hsum := sum_le_sum (s := (univ : Finset (Fin n))) (fun a _ => hmin (0, a))
    rw [sum_freq, hF] at hsum
    simp only [sum_const, card_univ, Fintype.card_fin, smul_eq_mul] at hsum
    by_contra! h
    have hmore := Nat.mul_le_mul_left n (show s+1 ≤ m by omega)
    change n*m ≤ n*s+k at hsum
    rw [mul_add, mul_one] at hmore
    omega
  obtain ⟨i, hi⟩ := coord_outside {x.1} (by simp)
  have hxi : x.1 ≠ i := by simpa [ne_comm] using hi
  obtain ⟨j, l, hxj, hxl, hij, hil, hjl⟩ := other_coordinates x.1 i hxi
  obtain ⟨t, _, hb, _, _⟩ := matching_frequency_bound hD hM (m := m) rfl hmin
    hxi hxj hxl hij hil hjl
  rw [hF] at hb
  change 2 * (n*s+k) ≥ 2*m^2 + (n-m)^2 + ((n-m)-t)^2 at hb
  have hh : 2*m^2 + (n-m)^2 ≤ 2 * (n*s+k) := by omega
  have hq : n-m = 2*s+(s-m) := by omega
  rw [hq, hn] at hh
  refine ⟨x, hmin, hlow, ?_⟩
  change 3*(s-m)^2 ≤ 2*k
  generalize hd : s-m = d at hh ⊢
  rw [show s = m+d by omega] at hh
  nlinarith

/-- Lean verification of the one-cell gap for all orders \(3s\), \(s\ge2\). -/
theorem no_plus_one {s : ℕ} (hs : 2 ≤ s)
    (hD : Linear D) (hM : Saturated D) (hn : n = 3*s) :
    D.card ≠ 3*s^2+1 := by
  intro h
  have hF : D.card = n*s+1 := by rw [h, hn]; ring
  obtain ⟨x, hmin, hm, hbound⟩ := minimum_deficit hD hM hs hn (by decide : 1 ≤ 2) hF
  have hxs : freq D x = s := by
    by_contra! he
    have hpos : 1 ≤ s - freq D x := by omega
    have hp := Nat.pow_le_pow_left hpos 2
    norm_num at hp
    omega
  apply exclude_with_minimum hD hM (fun y => hxs ▸ hmin y) hF hn
  · omega
  · decide
  · decide


/-- The frequency in one coordinate is at least the baseline for every
label plus the extra contribution from a specified set of values. -/
private theorem frequency_uplift {m e : ℕ} (hf : ∀ x, m ≤ freq D x)
    (i : Coord) (A : Finset (Fin n)) (hA : ∀ a ∈ A, m+e ≤ freq D (i, a)) :
    n*m + A.card*e ≤ D.card := by
  classical
  have hsum := sum_le_sum (s := (univ : Finset (Fin n)))
    (f := fun a => m + if a ∈ A then e else 0)
    (g := fun a => freq D (i, a)) (by
      intro a _
      by_cases ha : a ∈ A
      · simpa [ha] using hA a ha
      · simpa [ha] using hf (i, a))
  rw [sum_freq, sum_add_distrib, ← sum_filter] at hsum
  simpa [sum_const, smul_eq_mul] using hsum

/-- At size \(3s^2+2\) the minimum is \(s-1\). Every neighbor
of a minimum label is minimum, and every cross-coordinate pair of
minimum labels is used. -/
theorem plus_two_minimum_structure {s : ℕ} (hs : 3 ≤ s)
    (hD : Linear D) (hM : Saturated D) (hn : n = 3*s) (hF : D.card = n*s+2) :
    (∃ x : Label n, freq D x = s-1) ∧
    (∀ x, s-1 ≤ freq D x) ∧
    (∀ {x y : Label n}, Used D x y → freq D x = s-1 → freq D y = s-1) ∧
    (∀ {x y : Label n}, x.1 ≠ y.1 →
      freq D x = s-1 → freq D y = s-1 → Used D x y) := by
  obtain ⟨z, hzmin, hzle, hdef⟩ := minimum_deficit hD hM (by omega) hn (by decide) hF
  have hzge : s-1 ≤ freq D z := by
    by_contra! h
    have hpos : 2 ≤ s-freq D z := by omega
    have hp := Nat.pow_le_pow_left hpos 2
    norm_num at hp
    omega
  have hzne : freq D z ≠ s := by
    intro he
    exact exclude_with_minimum hD hM (fun y => he ▸ hzmin y) hF hn
      (by omega) (by decide) (by decide)
  have hz : freq D z = s-1 := by omega
  have hf (x : Label n) : s-1 ≤ freq D x := hz ▸ hzmin x
  refine ⟨⟨z, hz⟩, hf, ?_, ?_⟩
  · intro x y hxy hx
    obtain ⟨j, k, hxj, hxk, hyj, hyk, hjk⟩ := other_coordinates x.1 y.1 hxy.1
    obtain ⟨t, ht, hb, hperf, heq⟩ :=
      matching_frequency_bound hD hM hx hf hxy.1 hxj hxk hyj hyk hjk
    have hq : n-(s-1) = 2*s+1 := by omega
    have hscore : 2*(n*s+2) = 2*(s-1)^2 + (2*s+1)^2 + 1 := by
      generalize hd : s-1 = d
      rw [hn, show s = d+1 by omega]
      ring
    rw [hF, hq, hscore] at hb
    rw [hq] at ht hperf
    have hnp : t ≠ 2*s+1 := by
      intro he
      have hU : (unused D x k).card = 2*s+1 := by rw [card_unused hD hxk, hx, hq]
      have hlow := sum_le_sum (s := (neighbors D x k)) (fun a _ => hf (k, a))
      rw [sum_const, smul_eq_mul, card_neighbors hD hxk, hx] at hlow
      have hhigh := sum_le_sum (s := (unused D x k)) (fun a ha =>
        show s+1 ≤ freq D (k, a) by have := hperf he a ha; omega)
      rw [sum_const, smul_eq_mul, hU] at hhigh
      have htot := sum_split (D := D) (x := x) (i := k) (M := ∅) (empty_subset _)
      simp only [sum_empty, add_zero, sdiff_empty] at htot
      have hlimit : (s-1)*(s-1)+(2*s+1)*(s+1) ≤ n*s+2 := by omega
      generalize hd : s-1 = d at hlimit
      rw [hn, show s = d+1 by omega] at hlimit
      nlinarith
    have hdiff : (2*s+1-t)^2 = 1 := by
      have hd : 1 ≤ 2*s+1-t := by omega
      have hp := Nat.pow_le_pow_left hd 2
      norm_num at hp
      omega
    apply heq (by rw [hF, hq, hscore, hdiff])
    exact (mem_neighbors hxy.1).2 (by simpa using hxy)
  · intro x y hxy hx hy
    by_contra hab
    obtain ⟨i, j, hxi, hxj, hyi, hyj, hij⟩ := other_coordinates x.1 y.1 hxy
    have hci := card_candidates_lower hD (x := x) (y := y) hxi hyi
    have hcj := card_candidates_lower hD (x := x) (y := y) hxj hyj
    rw [hx, hy] at hci hcj
    have hlarge : s+2 ≤ (candidates D x y i).card := by omega
    have hsum := frequency_uplift hf i (candidates D x y i) (e := 3) (by
      intro a ha
      have hb := card_candidates_le_freq hD hij fun b hb =>
        candidate_rectangle hM hxy hxi hxj hyi hyj hij hab ha hb
      omega)
    have hh := Nat.mul_le_mul_right 3 hlarge
    have hbase : n*s = n*(s-1)+n := by
      conv_lhs => rw [show s = (s-1)+1 by omega]
      rw [mul_add, mul_one]
    omega


/-- At order six, the matching bound gives at least twelve words. At
equality the minimum label frequency must be two. -/
private theorem six_bound_at_equality {D : Design 6} (hD : Linear D)
    (hM : Saturated D) : 12 ≤ D.card ∧ (D.card = 12 → ∀ x, 2 ≤ freq D x) := by
  classical
  let initial : Label 6 := (0, 0)
  obtain ⟨x, _, hmin⟩ := exists_min_image (univ : Finset (Label 6)) (freq D)
    ⟨initial, mem_univ _⟩
  obtain ⟨i, hi⟩ := coord_outside {x.1} (by simp)
  have hxi : x.1 ≠ i := by simpa [ne_comm] using hi
  obtain ⟨j, k, hxj, hxk, hij, hik, hjk⟩ := other_coordinates x.1 i hxi
  let m := freq D x
  have hm : m ≤ 6 := by
    rw [show m = freq D x from rfl, ← card_neighbors hD hxi]
    simpa using card_le_univ (s := neighbors D x i)
  obtain ⟨t, _, hb, _, _⟩ := matching_frequency_bound hD hM (m := m) rfl
    (fun y => hmin y (mem_univ _)) hxi hxj hxk hij hik hjk
  have hscore : 2*m^2+(6-m)^2 ≤ 2*D.card := by omega
  have h : 12 ≤ D.card ∧ (D.card = 12 → 2 ≤ m) := by
    interval_cases m <;> norm_num at hscore ⊢ <;> omega
  exact ⟨h.1, fun hs y => (h.2 hs).trans (hmin y (mem_univ _))⟩

/-- The 12-word equality case would partition the words into three blocks,
each supporting at most two words over its two values per coordinate. -/
private theorem six_no_twelve {D : Design 6} (hD : Linear D)
    (hM : Saturated D) (hF : D.card = 12) : False := by
  classical
  have hmin := (six_bound_at_equality hD hM).2 hF
  have he (x : Label 6) : freq D x = 2 := by
    by_contra! h
    have hhigh : x.2 ∈ (univ : Finset (Fin 6)).filter (fun a => 2 < freq D (x.1, a)) :=
      mem_filter.mpr ⟨mem_univ _, by simpa using lt_of_le_of_ne (hmin x) (Ne.symm h)⟩
    have hlimit : ((univ : Finset (Fin 6)).filter (fun a => 2 < freq D (x.1, a))).card ≤ 0 :=
      high_card_le hmin (s := 2) (k := 0) (by simpa using hF) x.1
    have hpos := card_pos.mpr ⟨x.2, hhigh⟩
    omega
  obtain ⟨block, hblock, hstay⟩ := three_blocks hD hM hmin (k := 0)
    (by simpa using hF) (by decide) (by decide)
  let T (b : Fin 3) := D.filter fun w => block (0, w 0) = b
  have hsum : ∑ b : Fin 3, (T b).card = D.card := by
    simpa only [T, mem_univ, filter_true] using
      sum_card_fiberwise_eq_card_filter D (univ : Finset (Fin 3))
        (fun w => block (0, w 0))
  have hT (b : Fin 3) : (T b).card ≤ 2 := by
    apply small_projection_card hD (filter_subset _ _)
    intro i
    rw [← hblock i b]
    apply card_le_card
    intro a ha
    obtain ⟨w, hw, rfl⟩ := mem_image.mp ha
    obtain ⟨hwD, hwb⟩ := mem_filter.mp hw
    apply mem_filter.mpr
    refine ⟨mem_univ _, ?_⟩
    by_cases hi : i = 0
    · simpa [hi] using hwb
    · exact (hstay (he (i, w i)) ⟨hi, w, hwD, rfl, rfl⟩).trans hwb
  have htotal := sum_le_sum (s := (univ : Finset (Fin 3))) (fun b _ => hT b)
  rw [hsum, hF] at htotal
  norm_num at htotal

/-- A maximal order-six arrangement cannot contain fewer than fourteen words.
The remaining obstruction at fourteen is addressed in the Euler note. -/
theorem six_lower_bound {D : Design 6} (hD : Linear D) (hM : Saturated D) :
    14 ≤ D.card := by
  have hb := (six_bound_at_equality hD hM).1
  have h12 : D.card ≠ 12 := six_no_twelve hD hM
  have h13 : D.card ≠ 13 := no_plus_one (s := 2) (by decide) hD hM (by decide)
  omega


/-- The labels of a specified frequency in one coordinate. -/
def frequencyLabels (D : Design n) (f : ℕ) (i : Coord) : Finset (Fin n) :=
  univ.filter fun a => freq D (i, a) = f

/-- A full block has exactly the specified number of labels in each
coordinate and uses every pair of its labels from distinct coordinates. -/
def FullFrequencyBlock (D : Design n) (f : ℕ) : Prop :=
  (∀ i, (frequencyLabels D f i).card = f) ∧
  ∀ {x y : Label n}, x.1 ≠ y.1 → freq D x = f → freq D y = f → Used D x y

/-- If all labels of a positive frequency are linked to one another
across distinct coordinates, and have no neighbors of another
frequency, then they form a full block. -/
private theorem full_of_neighbors {f : ℕ} (hD : Linear D) (hf : 0 < f)
    (hex : ∃ x : Label n, freq D x = f)
    (hclosed : ∀ {x y : Label n}, Used D x y → freq D x = f → freq D y = f)
    (hcomplete : ∀ {x y : Label n}, x.1 ≠ y.1 →
      freq D x = f → freq D y = f → Used D x y) : FullFrequencyBlock D f := by
  classical
  obtain ⟨z, hz⟩ := hex
  have hsome (i : Coord) : ∃ a : Fin n, freq D (i, a) = f := by
    by_cases hi : z.1 = i
    · exact ⟨z.2, by simpa [← hi] using hz⟩
    · have hc := card_neighbors hD hi
      rw [hz] at hc
      obtain ⟨a, ha⟩ := card_pos.mp (by omega : 0 < (neighbors D z i).card)
      exact ⟨a, hclosed ((mem_neighbors hi).1 ha) hz⟩
  refine ⟨?_, hcomplete⟩
  intro i
  obtain ⟨j, hj⟩ := coord_outside {i} (by simp)
  have hji : j ≠ i := by simpa using hj
  obtain ⟨b, hb⟩ := hsome j
  have heq : frequencyLabels D f i = neighbors D (j, b) i := by
    ext a
    rw [mem_neighbors hji]
    simp only [frequencyLabels, mem_filter, mem_univ, true_and]
    exact ⟨hcomplete hji hb, (hclosed · hb)⟩
  rw [heq, card_neighbors hD hji, hb]

/-- At size \(3s^2+2\), the \(s-1\) frequency labels form a full
orthogonal block, separated from all the remaining labels. -/
private theorem plus_two_small_block {s : ℕ} (hs : 3 ≤ s)
    (hD : Linear D) (hM : Saturated D) (hn : n = 3*s) (hF : D.card = n*s+2) :
    FullFrequencyBlock D (s-1) ∧
    ∀ {x y : Label n}, Used D x y → freq D x = s-1 → freq D y = s-1 := by
  obtain ⟨hex, _, hclosed, hcomplete⟩ := plus_two_minimum_structure hs hD hM hn hF
  exact ⟨full_of_neighbors hD (by omega) hex hclosed hcomplete, hclosed⟩


/-- With the smallest block removed, each other coordinate has \(2s+1\)
labels. The candidate rectangle with a label from the removed block
forces the two remaining frequency classes. -/
private theorem plus_two_pivot {s : ℕ} (hs : 3 ≤ s)
    (hD : Linear D) (hM : Saturated D) (hn : n = 3*s) (hF : D.card = n*s+2) :
    (∃ x : Label n, freq D x = s) ∧
    ∀ {x : Label n}, freq D x = s →
      (∀ i, x.1 ≠ i → (frequencyLabels D s i).card = s ∧
        (frequencyLabels D (s+1) i).card = s+1 ∧
        ∀ a : Fin n, freq D (i, a) = s-1 ∨ freq D (i, a) = s ∨ freq D (i, a) = s+1) ∧
      (∀ {y z : Label n}, x.1 ≠ y.1 → x.1 ≠ z.1 →
        Used D y z → freq D y = freq D z) := by
  classical
  obtain ⟨_, hmin, _, _⟩ := plus_two_minimum_structure hs hD hM hn hF
  obtain ⟨hsmall, hclosed⟩ := plus_two_small_block hs hD hM hn hF
  let A (i : Coord) := univ \ frequencyLabels D (s-1) i
  have allowed {i : Coord} {a : Fin n} : a ∈ A i ↔ s ≤ freq D (i, a) := by
    have hh := hmin (i, a)
    simp only [A, frequencyLabels, mem_sdiff, mem_filter, mem_univ, true_and]
    omega
  have hA (i : Coord) : (A i).card = 2*s+1 := by
    dsimp [A]
    rw [card_sdiff_of_subset (subset_univ _), hsmall.1, card_univ, Fintype.card_fin]
    omega
  have sumA (i : Coord) : (∑ a ∈ A i, freq D (i, a)) = s*s+(s+1)*(s+1) := by
    have hL : (∑ a ∈ frequencyLabels D (s-1) i, freq D (i, a)) = (s-1)*(s-1) := by
      calc
        _ = ∑ _ ∈ frequencyLabels D (s-1) i, (s-1) := by
          apply sum_congr rfl
          intro a ha
          exact (mem_filter.mp ha).2
        _ = _ := by simp [sum_const, smul_eq_mul, hsmall.1]
    have hSum := sum_sdiff (f := fun a : Fin n => freq D (i, a))
      (subset_univ (frequencyLabels D (s-1) i))
    change (∑ a ∈ A i, freq D (i, a)) + _ = _ at hSum
    rw [hL, sum_freq, hF] at hSum
    have ht : n*s+2 = (s-1)*(s-1)+(s*s+(s+1)*(s+1)) := by
      rw [hn]
      generalize he : s-1 = u
      rw [show s = u+1 by omega]
      ring
    omega
  let Q := 2*s+1
  let allowedLabels := (univ : Finset (Label n)).filter fun x => s ≤ freq D x
  have hnonempty : allowedLabels.Nonempty := by
    obtain ⟨a, ha⟩ := card_pos.mp (by rw [hA]; omega : 0 < (A 0).card)
    exact ⟨(0,a), mem_filter.mpr ⟨mem_univ _, allowed.mp ha⟩⟩
  obtain ⟨v, hv, hvmin⟩ := exists_min_image allowedLabels (freq D) hnonempty
  have lower (y : Label n) (hy : s ≤ freq D y) : freq D v ≤ freq D y :=
    hvmin y (mem_filter.mpr ⟨mem_univ _, hy⟩)
  have hvle : freq D v ≤ s := by
    by_contra! hn
    have hfreq := sum_le_sum (s := A 0) (fun a ha =>
      (show s+1 ≤ freq D v by omega).trans (lower (0,a) (allowed.mp ha)))
    rw [sum_const, smul_eq_mul, hA, sumA] at hfreq
    nlinarith
  have hvs : freq D v = s := le_antisymm hvle (mem_filter.mp hv).2
  refine ⟨⟨v, hvs⟩, ?_⟩
  intro x hx
  let N (i : Coord) := neighbors D x i
  let U (i : Coord) := A i \ N i
  have hnsub (i : Coord) (hi : x.1 ≠ i) : N i ⊆ A i := by
    intro a ha
    apply allowed.2
    have hu := (mem_neighbors hi).1 ha
    have hno : freq D (i, a) ≠ s-1 := by
      intro he
      have := hclosed (used_symm hu) he
      omega
    have := hmin (i,a)
    omega
  have hN (i : Coord) (hi : x.1 ≠ i) : (N i).card = s := by
    rw [show N i = neighbors D x i from rfl, card_neighbors hD hi, hx]
  have hU (i : Coord) (hi : x.1 ≠ i) : (U i).card = s+1 := by
    rw [show U i = A i \ N i from rfl, card_sdiff_of_subset (hnsub i hi), hA, hN i hi]
    omega
  have rect {i j : Coord} (hi : x.1 ≠ i) (hj : x.1 ≠ j) (hij : i ≠ j)
      {a b : Fin n} (ha : a ∈ U i) (hb : b ∈ U j) : Used D (i,a) (j,b) := by
    obtain ⟨k, hk⟩ := coord_outside {x.1,i,j} (by simp [hi, hj, hij])
    simp only [mem_insert, mem_singleton, not_or] at hk
    obtain ⟨c, hc⟩ := card_pos.mp (by rw [hsmall.1]; omega :
      0 < (frequencyLabels D (s-1) k).card)
    have hcl : freq D (k,c) = s-1 := (mem_filter.mp hc).2
    have hky {y : Label n} (hy : s ≤ freq D y) : ¬ Used D (k,c) y := by
      intro he
      have := hclosed he hcl
      omega
    have ha' := mem_sdiff.mp ha
    have hb' := mem_sdiff.mp hb
    apply candidate_rectangle hM (Ne.symm hk.1) hi hj hk.2.1 hk.2.2 hij
      (fun he => hky ((by omega : s ≤ freq D x)) (used_symm he))
    · exact (mem_candidates hi hk.2.1).2
        ⟨fun he => ha'.2 ((mem_neighbors hi).2 he), hky (allowed.mp ha'.1)⟩
    · exact (mem_candidates hj hk.2.2).2
        ⟨fun he => hb'.2 ((mem_neighbors hj).2 he), hky (allowed.mp hb'.1)⟩
  have classes (i : Coord) (hi : x.1 ≠ i) :
      (∀ a ∈ N i, freq D (i,a) = s) ∧ (∀ a ∈ U i, freq D (i,a) = s+1) := by
    obtain ⟨j, k, hj, _, hij, _, _⟩ := other_coordinates x.1 i hi
    have hu (a : Fin n) (ha : a ∈ U i) : s+1 ≤ freq D (i,a) := by
      rw [← hU j hj, ← card_neighbors hD hij]
      apply card_le_card
      intro b hb
      exact (mem_neighbors hij).2 (rect hi hj hij ha hb)
    have hn (a : Fin n) (ha : a ∈ N i) : s ≤ freq D (i,a) := allowed.mp (hnsub i hi ha)
    have hsum := sum_sdiff (f := fun a => freq D (i,a)) (hnsub i hi)
    rw [sumA] at hsum
    change (∑ a ∈ U i, freq D (i,a)) + (∑ a ∈ N i, freq D (i,a)) = _ at hsum
    have hn_sum : s*s ≤ ∑ a ∈ N i, freq D (i,a) := by
      simpa [sum_const, smul_eq_mul, hN i hi] using sum_le_sum hn
    have hu_sum : (s+1)*(s+1) ≤ ∑ a ∈ U i, freq D (i,a) := by
      simpa [sum_const, smul_eq_mul, hU i hi] using sum_le_sum hu
    constructor
    · intro a ha
      apply le_antisymm _ (hn a ha)
      by_contra! hh
      have hstrict : s*s < ∑ a ∈ N i, freq D (i,a) := by
        simpa [sum_const, smul_eq_mul, hN i hi] using sum_lt_sum hn ⟨a,ha,hh⟩
      omega
    · intro a ha
      apply le_antisymm _ (hu a ha)
      by_contra! hh
      have hstrict : (s+1)*(s+1) < ∑ a ∈ U i, freq D (i,a) := by
        simpa [sum_const, smul_eq_mul, hU i hi] using sum_lt_sum hu ⟨a,ha,hh⟩
      omega
  have partition {i : Coord} {a : Fin n} (ha : a ∈ A i) :
      a ∈ N i ∨ a ∈ U i := by
    by_cases hn : a ∈ N i
    · exact Or.inl hn
    · exact Or.inr (mem_sdiff.mpr ⟨ha,hn⟩)
  refine ⟨?_, ?_⟩
  · intro i hi
    have hN' : frequencyLabels D s i = N i := by
      ext a
      simp only [frequencyLabels, mem_filter, mem_univ, true_and]
      refine ⟨?_, (classes i hi).1 a⟩
      intro hf
      rcases partition (allowed.2 (by omega : s ≤ freq D (i,a))) with he | he
      · exact he
      · have := (classes i hi).2 a he
        omega
    have hU' : frequencyLabels D (s+1) i = U i := by
      ext a
      simp only [frequencyLabels, mem_filter, mem_univ, true_and]
      refine ⟨?_, (classes i hi).2 a⟩
      intro hf
      rcases partition (allowed.2 (by omega : s ≤ freq D (i,a))) with he | he
      · have := (classes i hi).1 a he
        omega
      · exact he
    refine ⟨by rw [hN', hN i hi], by rw [hU', hU i hi], ?_⟩
    intro a
    by_cases ha : a ∈ A i
    · rcases partition ha with hn | hu
      · exact Or.inr (Or.inl ((classes i hi).1 a hn))
      · exact Or.inr (Or.inr ((classes i hi).2 a hu))
    · have := hmin (i,a)
      have hh := mt allowed.2 ha
      exact Or.inl (by omega)
  · intro y z hy hz hused
    by_cases hl : freq D y = s-1
    · exact hl.trans (hclosed hused hl).symm
    by_cases hr : freq D z = s-1
    · exact False.elim (hl (hclosed (used_symm hused) hr))
    have hyA : y.2 ∈ A y.1 := allowed.2 (by change s ≤ freq D y; have := hmin y; omega)
    have hzA : z.2 ∈ A z.1 := allowed.2 (by change s ≤ freq D z; have := hmin z; omega)
    have force {i j : Coord} (hi : x.1 ≠ i) (hj : x.1 ≠ j) (hij : i ≠ j)
        {a b : Fin n} (ha : a ∈ U i) (hb : Used D (i,a) (j,b)) : b ∈ U j := by
      have hsub : U j ⊆ neighbors D (i,a) j := by
        intro b hb
        exact (mem_neighbors hij).2 (rect hi hj hij ha hb)
      have hcap : (neighbors D (i,a) j).card ≤ (U j).card := by
        rw [card_neighbors hD hij, (classes i hi).2 a ha, hU j hj]
      exact (eq_of_subset_of_card_le hsub hcap).symm ▸ (mem_neighbors hij).2 hb
    rcases partition hyA with hyn | hyu
    · rcases partition hzA with hzn | hzu
      · exact ((classes _ hy).1 _ hyn).trans ((classes _ hz).1 _ hzn).symm
      · have he := force hz hy hused.1.symm hzu (used_symm hused)
        exact False.elim ((mem_sdiff.mp he).2 hyn)
    · have hzu := force hy hz hused.1 hyu hused
      exact ((classes _ hy).2 _ hyu).trans ((classes _ hz).2 _ hzu).symm


/-- A maximal design of size \(3s^2+2\) at order \(3s\) splits into three
full blocks. Each word stays within one frequency class, of size
\(s-1\), \(s\), or \(s+1\) in every coordinate. -/
theorem classify_plus_two {s : ℕ} (hs : 3 ≤ s)
    (hD : Linear D) (hM : Saturated D) (hn : n = 3*s) (hF : D.card = 3*s^2+2) :
    FullFrequencyBlock D (s-1) ∧ FullFrequencyBlock D s ∧
    FullFrequencyBlock D (s+1) ∧
    (∀ x : Label n, freq D x = s-1 ∨ freq D x = s ∨ freq D x = s+1) ∧
    (∀ w ∈ D, ∀ i j : Coord, freq D (i,w i) = freq D (j,w j)) := by
  classical
  have hF' : D.card = n*s+2 := by rw [hF,hn]; ring
  obtain ⟨hsmall, _⟩ := plus_two_small_block hs hD hM hn hF'
  obtain ⟨⟨x, hx⟩, pivot⟩ := plus_two_pivot hs hD hM hn hF'
  have hpf (i : Coord) (hi : x.1 ≠ i) : ∃ a : Fin n, freq D (i,a) = s := by
    have hp := (pivot hx).1 i hi
    have hc : 0 < (frequencyLabels D s i).card := by rw [hp.1]; omega
    obtain ⟨a, ha⟩ := card_pos.mp hc
    exact ⟨a, (mem_filter.mp ha).2⟩
  have stat (i : Coord) : (frequencyLabels D s i).card = s ∧
      (frequencyLabels D (s+1) i).card = s+1 ∧
      ∀ a : Fin n, freq D (i,a) = s-1 ∨ freq D (i,a) = s ∨ freq D (i,a) = s+1 := by
    by_cases hi : x.1 = i
    · obtain ⟨j, hj⟩ := coord_outside {x.1} (by simp)
      have hxj : x.1 ≠ j := by simpa [ne_comm] using hj
      obtain ⟨a, ha⟩ := hpf j hxj
      exact (pivot (x := (j,a)) ha).1 i (by simpa [← hi] using hxj.symm)
    · exact (pivot hx).1 i hi
  have stay {y z : Label n} (hu : Used D y z) : freq D y = freq D z := by
    have hsize : ({x.1,y.1,z.1} : Finset Coord).card < 4 := by
      have h1 := card_insert_le (s := ({y.1,z.1} : Finset Coord)) x.1
      have h2 := card_insert_le (s := ({z.1} : Finset Coord)) y.1
      simp only [card_singleton] at h2
      omega
    obtain ⟨k,hk⟩ := coord_outside _ hsize
    simp only [mem_insert, mem_singleton, not_or] at hk
    obtain ⟨a,ha⟩ := hpf k (Ne.symm hk.1)
    exact (pivot (x := (k,a)) ha).2 hk.2.1 hk.2.2 hu
  have full {f : ℕ} (hc : ∀ i, (frequencyLabels D f i).card = f) :
      FullFrequencyBlock D f := by
    refine ⟨hc, ?_⟩
    intro y z hyz hy hz
    have hsub : neighbors D y z.1 ⊆ frequencyLabels D f z.1 := by
      intro a ha
      exact mem_filter.mpr
        ⟨mem_univ _, (stay ((mem_neighbors hyz).1 ha)).symm.trans hy⟩
    have hcap : (frequencyLabels D f z.1).card ≤ (neighbors D y z.1).card := by
      rw [hc, card_neighbors hD hyz, hy]
    have he := eq_of_subset_of_card_le hsub hcap
    have hz' : z.2 ∈ frequencyLabels D f z.1 := mem_filter.mpr ⟨mem_univ _, hz⟩
    rw [← he] at hz'
    exact (mem_neighbors hyz).1 hz'
  refine ⟨hsmall, full (fun i => (stat i).1), full (fun i => (stat i).2.1),
    (fun y => (stat y.1).2.2 y.2), ?_⟩
  intro w hw i j
  by_cases hij : i = j
  · simp [hij]
  · exact stay ⟨hij,w,hw,rfl,rfl⟩


/-- Three full blocks of the stated sizes give the converse. Pigeonhole
saturation uses four coordinates and three possible frequency classes. -/
theorem plus_two_of_full_blocks {s : ℕ} (hs : 3 ≤ s)
    (h1 : FullFrequencyBlock D (s-1)) (h2 : FullFrequencyBlock D s)
    (h3 : FullFrequencyBlock D (s+1))
    (hf : ∀ x : Label n, freq D x = s-1 ∨ freq D x = s ∨ freq D x = s+1) :
    Saturated D ∧ D.card = 3*s^2+2 := by
  classical
  have h12 : s-1 ≠ s := by omega
  have h13 : s-1 ≠ s+1 := by omega
  have h23 : s ≠ s+1 := by omega
  constructor
  · intro w
    let tag (i : Coord) : Fin 3 :=
      if freq D (i,w i) = s-1 then 0 else if freq D (i,w i) = s then 1 else 2
    obtain ⟨i,j,hij,he⟩ := Fintype.exists_ne_map_eq_of_card_lt tag (by decide)
    refine ⟨i,j,?_⟩
    rcases hf (i,w i) with ha | ha | ha <;> rcases hf (j,w j) with hb | hb | hb <;>
      simp [tag, ha, hb, Ne.symm h12, Ne.symm h13] at he <;>
      first | exact h1.2 hij ha hb | exact h2.2 hij ha hb | exact h3.2 hij ha hb
  · let L := frequencyLabels D (s-1) 0
    let M := frequencyLabels D s 0
    let H := frequencyLabels D (s+1) 0
    have hall : L ∪ M ∪ H = univ := by
      ext a
      simp only [L,M,H,frequencyLabels,mem_union,mem_filter,mem_univ,true_and,iff_true]
      rcases hf (0,a) with ha | ha | ha
      · exact Or.inl (Or.inl ha)
      · exact Or.inl (Or.inr ha)
      · exact Or.inr ha
    have hLM : Disjoint L M := by
      rw [Finset.disjoint_left]
      intro a ha hb
      exact h12 ((mem_filter.mp ha).2.symm.trans (mem_filter.mp hb).2)
    have hLH : Disjoint (L ∪ M) H := by
      rw [Finset.disjoint_left]
      intro a ha hb
      have hb' : freq D (0,a) = s+1 := (mem_filter.mp hb).2
      rcases mem_union.mp ha with ha | ha
      · exact h13 ((mem_filter.mp ha).2.symm.trans hb')
      · exact h23 ((mem_filter.mp ha).2.symm.trans hb')
    have totals (f : ℕ) (h : FullFrequencyBlock D f) :
        (∑ a ∈ frequencyLabels D f (0 : Coord), freq D (0,a)) = f*f := by
      calc
        _ = ∑ _ ∈ frequencyLabels D f (0 : Coord), f := by
          apply sum_congr rfl
          exact fun a ha => (mem_filter.mp ha).2
        _ = _ := by simp [sum_const,smul_eq_mul,h.1]
    have he := sum_freq D (0 : Coord)
    rw [← hall, sum_union hLH, sum_union hLM] at he
    change ((∑ a ∈ frequencyLabels D (s-1) 0, freq D (0,a)) +
      (∑ a ∈ frequencyLabels D s 0, freq D (0,a))) +
      (∑ a ∈ frequencyLabels D (s+1) 0, freq D (0,a)) = D.card at he
    rw [totals _ h1, totals _ h2, totals _ h3] at he
    rw [← he]
    generalize hd : s-1 = u
    rw [show s = u+1 by omega]
    ring

end LatinGap

#print axioms LatinGap.no_plus_one
#print axioms LatinGap.plus_two_minimum_structure
#print axioms LatinGap.six_lower_bound

#print axioms LatinGap.classify_plus_two

#print axioms LatinGap.plus_two_of_full_blocks
