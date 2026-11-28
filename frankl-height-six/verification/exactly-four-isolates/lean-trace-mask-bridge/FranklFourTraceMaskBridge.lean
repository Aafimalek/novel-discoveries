import FranklFourTraceCertificateDefinitions
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.BinaryRec
import Mathlib.Data.List.Nodup

/- Kernel-checked on pinned Lean 4.36 and Mathlib. -/
namespace FranklFourTraceCertificate

abbrev Label := Fin 4
abbrev Trace := Finset Label

def decode (t : Nat) : Trace :=
  Finset.univ.filter (fun i : Label => t.testBit i.val = true)

def encode (s : Trace) : Nat :=
  (if (0 : Label) ∈ s then 1 else 0) +
  (if (1 : Label) ∈ s then 2 else 0) +
  (if (2 : Label) ∈ s then 4 else 0) +
  (if (3 : Label) ∈ s then 8 else 0)

@[simp] theorem mem_decode {t : Nat} {i : Label} :
    i ∈ decode t ↔ t.testBit i.val = true := by
  simp [decode]

private theorem encode_lt_16_finite : ∀ s : Trace, encode s < 16 := by
  decide

private theorem decode_encode_finite : ∀ s : Trace, decode (encode s) = s := by
  decide

private theorem encode_decode_small : ∀ t : Fin 16, encode (decode t.val) = t.val := by
  decide

theorem encode_lt_16 (s : Trace) : encode s < 16 := encode_lt_16_finite s

@[simp] theorem decode_encode (s : Trace) : decode (encode s) = s :=
  decode_encode_finite s

theorem encode_decode {t : Nat} (ht : t < 16) : encode (decode t) = t :=
  encode_decode_small ⟨t,ht⟩

theorem decode_injOn : Set.InjOn decode {t : Nat | t < 16} := by
  intro a ha b hb h
  rw [← encode_decode ha, ← encode_decode hb, h]

@[simp] theorem decode_union (a b : Nat) :
    decode (a ||| b) = decode a ∪ decode b := by
  ext i
  simp only [mem_decode,Nat.testBit_or,Bool.or_eq_true_iff,Finset.mem_union]

@[simp] theorem decode_inter (a b : Nat) :
    decode (a &&& b) = decode a ∩ decode b := by
  ext i
  simp only [mem_decode,Nat.testBit_and,Bool.and_eq_true_iff,Finset.mem_inter]

theorem decode_subset_of_and {a b : Nat} (h : a &&& b = a) : decode a ⊆ decode b := by
  intro i hi
  have hh : i ∈ decode (a &&& b) := h.symm ▸ hi
  rw [decode_inter] at hh
  exact (Finset.mem_inter.mp hh).2

theorem decode_ssubset_of_strictBitSubset {a b : Nat}
    (ha : a < 16) (hb : b < 16) (h : StrictBitSubset a b) :
    decode a ⊂ decode b :=
  Finset.ssubset_iff_subset_ne.mpr
    ⟨decode_subset_of_and h.2, fun he => h.1 (decode_injOn ha hb he)⟩

theorem encode_union (s t : Trace) : encode (s ∪ t) = encode s ||| encode t := by
  have hlt : encode s ||| encode t < 16 :=
    Nat.or_lt_two_pow (n := 4) (encode_lt_16 s) (encode_lt_16 t)
  apply decode_injOn (encode_lt_16 (s ∪ t)) hlt
  simp

private theorem mandatory_code_finite : ∀ t : Fin 16,
    t.val ∈ mandatory ↔ 3 ≤ (decode t.val).card := by
  decide

private theorem partition_code_finite : ∀ t : Fin 16,
    t.val ∈ mandatory ∨ t.val ∈ optional := by
  decide

theorem mandatory_iff_card {t : Nat} (ht : t < 16) :
    t ∈ mandatory ↔ 3 ≤ (decode t).card := mandatory_code_finite ⟨t,ht⟩

theorem mandatory_or_optional {t : Nat} (ht : t < 16) :
    t ∈ mandatory ∨ t ∈ optional := partition_code_finite ⟨t,ht⟩

/-- Low-bit-first packing; unlike the trace classifier this works for a
symbolic, arbitrary family and does not enumerate all its possibilities. -/
def pack : List Bool → Nat
  | [] => 0
  | bit :: bits => Nat.bit bit (pack bits)

private theorem pack_lt_pow (bits : List Bool) : pack bits < 2 ^ bits.length := by
  induction bits with
  | nil => simp [pack]
  | cons bit bits ih =>
      simpa only [pack,List.length_cons,Nat.bit_lt_two_pow_succ_iff] using ih

private theorem testBit_pack (bits : List Bool) (i : Nat) :
    (pack bits).testBit i = (bits[i]?).getD false := by
  induction bits generalizing i with
  | nil => simp [pack]
  | cons bit bits ih =>
      cases i with
      | zero => simp [pack]
      | succ i =>
          simpa only [pack,Nat.testBit_bit_succ,List.getElem?_cons_succ] using ih i

def familyMask (F : Finset Trace) : Nat :=
  pack (optional.map (fun t => decide (decode t ∈ F)))

theorem familyMask_lt (F : Finset Trace) : familyMask F < 2048 := by
  have h := pack_lt_pow (optional.map (fun t => decide (decode t ∈ F)))
  simpa [familyMask,optional] using h

private theorem familyMask_bit_of_row (F : Finset Trace) {t i : Nat}
    (h : (t,i) ∈ optional.zipIdx) :
    (familyMask F).testBit i = decide (decode t ∈ F) := by
  have hget := List.mk_mem_zipIdx_iff_getElem?.mp h
  simp only [familyMask,testBit_pack,List.getElem?_map,hget,Option.map_some,Option.getD_some]

private theorem profile_sublist (m : Nat) : List.Sublist (profile m) (mandatory ++ optional) := by
  unfold profile
  apply List.Sublist.append_left _ mandatory
  have h := List.Sublist.map Prod.fst
    (List.filter_sublist (p := fun row => m.testBit row.2) (l := optional.zipIdx))
  simpa only [List.zipIdx_map_fst] using h

theorem profile_nodup (m : Nat) : (profile m).Nodup :=
  (profile_sublist m).nodup (by decide)

private theorem universe_mask_bounds :
    (mandatory ++ optional).all (fun t => decide (t < 16)) = true := by decide

theorem profile_lt_16 {m t : Nat} (ht : t ∈ profile m) : t < 16 :=
  of_decide_eq_true (List.all_eq_true.mp universe_mask_bounds t ((profile_sublist m).subset ht))

/-- Membership in the checked numeric list agrees exactly with membership
in the symbolic trace family, on the 4-bit trace universe. -/
theorem mem_profile_familyMask_iff {F : Finset Trace}
    (hF : ∀ s : Trace, 3 ≤ s.card → s ∈ F) {t : Nat} (ht : t < 16) :
    t ∈ profile (familyMask F) ↔ decode t ∈ F := by
  unfold profile
  constructor
  · intro hp
    rcases List.mem_append.mp hp with hman | hopt
    · exact hF _ ((mandatory_iff_card ht).mp hman)
    · obtain ⟨row,hr,he⟩ := List.mem_map.mp hopt
      obtain ⟨hr0,hr1⟩ := List.mem_filter.mp hr
      obtain ⟨r,i⟩ := row
      change r = t at he
      subst r
      rw [familyMask_bit_of_row F hr0] at hr1
      exact of_decide_eq_true hr1
  · intro hmem
    rcases mandatory_or_optional ht with hman | hopt
    · exact List.mem_append_left _ hman
    · have hrow : t ∈ optional.zipIdx.map Prod.fst := by
        simpa only [List.zipIdx_map_fst] using hopt
      obtain ⟨row,hr,he⟩ := List.mem_map.mp hrow
      obtain ⟨r,i⟩ := row
      change r = t at he
      subst r
      apply List.mem_append_right _
      refine List.mem_map.mpr ⟨(t,i),List.mem_filter.mpr ⟨hr,?_⟩,rfl⟩
      rw [familyMask_bit_of_row F hr]
      exact decide_eq_true hmem

/-- Concrete representation of any family containing the five mandatory
traces. The image does not identify two distinct list entries. -/
theorem familyMask_image_profile {F : Finset Trace}
    (hF : ∀ s : Trace, 3 ≤ s.card → s ∈ F) :
    ((profile (familyMask F)).toFinset.image decode) = F := by
  ext s
  constructor
  · intro hs
    obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hs
    have ht' : t ∈ profile (familyMask F) := List.mem_toFinset.mp ht
    exact (mem_profile_familyMask_iff hF (profile_lt_16 ht')).mp ht'
  · intro hs
    refine Finset.mem_image.mpr ⟨encode s, List.mem_toFinset.mpr ?_,decode_encode s⟩
    apply (mem_profile_familyMask_iff hF (encode_lt_16 s)).mpr
    simpa using hs

theorem exists_profile_representation {F : Finset Trace}
    (hF : ∀ s : Trace, 3 ≤ s.card → s ∈ F) :
    ∃ m < 2048, ((profile m).toFinset.image decode) = F :=
  ⟨familyMask F,familyMask_lt F,familyMask_image_profile hF⟩

private theorem card_profile_filter_image (m : Nat) (p : Nat → Bool) :
    (((profile m).filter p).toFinset.image decode).card =
      ((profile m).filter p).length := by
  have hinj : Set.InjOn decode (((profile m).filter p).toFinset : Set Nat) := by
    intro a ha b hb he
    have ha' := (List.mem_filter.mp (List.mem_toFinset.mp ha)).1
    have hb' := (List.mem_filter.mp (List.mem_toFinset.mp hb)).1
    exact decode_injOn (profile_lt_16 ha') (profile_lt_16 hb') he
  rw [Finset.card_image_of_injOn hinj, List.toFinset_card_of_nodup]
  exact (profile_nodup m).filter p

theorem card_familyMask_profile {F : Finset Trace}
    (hF : ∀ s : Trace, 3 ≤ s.card → s ∈ F) :
    F.card = (profile (familyMask F)).length := by
  have h := card_profile_filter_image (familyMask F) (fun _ => true)
  rw [List.filter_true, familyMask_image_profile hF] at h
  exact h

theorem frequency_familyMask_profile {F : Finset Trace} (i : Label)
    (hF : ∀ s : Trace, 3 ≤ s.card → s ∈ F) :
    (F.filter (i ∈ ·)).card = traceFrequency (familyMask F) i.val := by
  let m := familyMask F
  let p := fun t : Nat => t.testBit i.val
  have he : ((profile m).filter p).toFinset.image decode = F.filter (i ∈ ·) := by
    ext s
    constructor
    · intro hs
      obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hs
      obtain ⟨ht',hit⟩ := List.mem_filter.mp (List.mem_toFinset.mp ht)
      exact Finset.mem_filter.mpr
        ⟨(mem_profile_familyMask_iff hF (profile_lt_16 ht')).mp ht',mem_decode.mpr hit⟩
    · intro hs
      obtain ⟨hsF,his⟩ := Finset.mem_filter.mp hs
      refine Finset.mem_image.mpr ⟨encode s,List.mem_toFinset.mpr (List.mem_filter.mpr
        ⟨?_,?_⟩),decode_encode s⟩
      · apply (mem_profile_familyMask_iff hF (encode_lt_16 s)).mpr
        simpa using hsF
      · change (encode s).testBit i.val = true
        exact mem_decode.mp (by simpa using his)
  have h := card_profile_filter_image m p
  rw [he] at h
  exact h

theorem familyMask_eligible {F : Finset Trace}
    (hF : ∀ s : Trace, 3 ≤ s.card → s ∈ F)
    (hUnion : ∀ ⦃s t⦄, s ∈ F → t ∈ F → s ∪ t ∈ F)
    (hLow : 2 * (F.filter ((0 : Label) ∈ ·)).card < F.card) :
    eligibleB (familyMask F) = true := by
  unfold eligibleB
  apply Bool.and_eq_true_iff.mpr
  constructor
  · exact decide_eq_true (by
      have hFreq := frequency_familyMask_profile 0 hF
      change (F.filter ((0 : Label) ∈ ·)).card = traceFrequency (familyMask F) 0 at hFreq
      rw [← card_familyMask_profile hF, ← hFreq]
      exact hLow)
  · unfold unionClosedB
    apply List.all_eq_true.mpr
    intro t ht
    apply List.all_eq_true.mpr
    intro u hu
    have htF := (mem_profile_familyMask_iff hF (profile_lt_16 ht)).mp ht
    have huF := (mem_profile_familyMask_iff hF (profile_lt_16 hu)).mp hu
    have huv : t ||| u < 16 :=
      Nat.or_lt_two_pow (n := 4) (profile_lt_16 ht) (profile_lt_16 hu)
    have hmem : (t ||| u) ∈ profile (familyMask F) :=
      (mem_profile_familyMask_iff hF huv).mpr (by
        rw [decode_union]
        exact hUnion htF huF)
    simpa using hmem

/-- Decode the union of all safe avoiding supports into labeled points. -/
def decodedSupport (m i j : Nat) : Trace :=
  Finset.univ.filter (fun k : Label => k.val ∈ supportBits m i j)

theorem mem_decodedSupport_iff {m i j : Nat} {k : Label} :
    k ∈ decodedSupport m i j ↔ ∃ t ∈ safeAvoiding m i j, k ∈ decode t := by
  simp [decodedSupport,supportBits,List.any_eq_true]

theorem decodedSupport_card (m i j : Nat) :
    (decodedSupport m i j).card = (supportBits m i j).length := by
  have he : (decodedSupport m i j).image Fin.val = (supportBits m i j).toFinset := by
    ext n
    constructor
    · intro h
      obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp h
      have hk' := (Finset.mem_filter.mp hk).2
      exact List.mem_toFinset.mpr hk'
    · intro h
      have hn := List.mem_toFinset.mp h
      have h4 : n < 4 := List.mem_range.mp (List.mem_filter.mp hn).1
      exact Finset.mem_image.mpr
        ⟨⟨n,h4⟩,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hn⟩,rfl⟩
  have hcard := Finset.card_image_of_injective (decodedSupport m i j) Fin.val_injective
  rw [he,List.toFinset_card_of_nodup] at hcard
  · exact hcard.symm
  · exact (List.nodup_range).filter _

theorem mem_safeAvoiding_of_bits {m t : Nat} {i j : Label}
    (ht : t < 16) (hi : i ∉ decode t) (hj : j ∉ decode t)
    (hcompat : ∀ u ∈ profile m, (t ||| u) ∈ profile m) :
    t ∈ safeAvoiding m i.val j.val := by
  have hbi : t.testBit i.val = false := by simpa [mem_decode] using hi
  have hbj : t.testBit j.val = false := by simpa [mem_decode] using hj
  apply List.mem_filter.mpr
  exact ⟨List.mem_range.mpr ht,by simpa [hbi,hbj] using hcompat⟩

theorem mem_safeAvoiding_iff {m t : Nat} {i j : Label} :
    t ∈ safeAvoiding m i.val j.val ↔
      t < 16 ∧ i ∉ decode t ∧ j ∉ decode t ∧
      (∀ u ∈ profile m, (t ||| u) ∈ profile m) := by
  simp [safeAvoiding,mem_decode,List.all_eq_true,and_assoc]

theorem decode_subset_decodedSupport {m i j t : Nat} (ht : t ∈ safeAvoiding m i j) :
    decode t ⊆ decodedSupport m i j := by
  intro k hk
  exact mem_decodedSupport_iff.mpr ⟨t,ht,hk⟩

theorem decodedSupport_subset_bottom {m i j c : Nat}
    (hcover : (safeAvoiding m i j).all (fun t => (t &&& c) == t) = true) :
    decodedSupport m i j ⊆ decode c := by
  intro k hk
  obtain ⟨t,ht,hkt⟩ := mem_decodedSupport_iff.mp hk
  have he : t &&& c = t := by simpa using List.all_eq_true.mp hcover t ht
  exact decode_subset_of_and he hkt

#print axioms decode_encode
#print axioms encode_union
#print axioms decode_ssubset_of_strictBitSubset
#print axioms exists_profile_representation
#print axioms card_familyMask_profile
#print axioms frequency_familyMask_profile
#print axioms familyMask_eligible
#print axioms decodedSupport_card
#print axioms mem_safeAvoiding_of_bits
#print axioms mem_safeAvoiding_iff
#print axioms decodedSupport_subset_bottom
end FranklFourTraceCertificate
