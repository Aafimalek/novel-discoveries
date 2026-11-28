/- Static draft. Reusable lexicographic production numbering for the
actual EndpointConcreteSpec dictionary. No compiler has run. -/
import EndpointConcreteSpec

namespace ES33.EndpointConcrete.OrientationRank

open ES33.Numbering

def before {n : Nat} (i : Fin n) : List (Fin n) := (List.finRange n).take i.val

def after {n : Nat} (i : Fin n) : List (Fin n) := (List.finRange n).drop (i.val+1)

def gtLabels {n : Nat} (i : Fin n) (xs : List (Fin n)) : List (Fin n) :=
  xs.filter fun j => decide (i<j)

private theorem val_get {n k : Nat} (hk : k < (List.finRange n).length) :
    ((List.finRange n)[k]).val = k := by simp [List.getElem_finRange]

private theorem before_length {n : Nat} (i : Fin n) : (before i).length = i.val := by
  simp [before,Nat.min_eq_left (Nat.le_of_lt i.isLt)]

private theorem after_length {n : Nat} (i : Fin n) :
    (after i).length = n-(i.val+1) := by
  simp [after]

private theorem before_lt {n : Nat} {i x : Fin n} (h : x ∈ before i) : x<i := by
  obtain ⟨k,hk,e⟩ := List.mem_take_iff_getElem.mp h
  have hkn : k < (List.finRange n).length := Nat.lt_of_lt_of_le hk (Nat.min_le_right _ _)
  have hki := Nat.lt_of_lt_of_le hk (Nat.min_le_left _ _)
  have hval := (val_get hkn).symm.trans (congrArg (fun y : Fin n => y.val) e)
  change x.val<i.val
  omega

private theorem lt_after {n : Nat} {i x : Fin n} (h : x ∈ after i) : i<x := by
  obtain ⟨k,hk,e⟩ := List.mem_drop_iff_getElem.mp h
  have hkn : (i.val+1)+k < (List.finRange n).length := by omega
  have hval := (val_get hkn).symm.trans (congrArg (fun y : Fin n => y.val) e)
  change i.val<x.val
  omega

private theorem fin_split {n : Nat} (i : Fin n) :
    List.finRange n = before i ++ (i :: after i) := by
  have h : i.val < (List.finRange n).length := by simp
  have e : (List.finRange n)[i.val] = i := Fin.ext (val_get h)
  calc
    List.finRange n = before i ++ (List.finRange n).drop i.val :=
      (List.take_append_drop i.val (List.finRange n)).symm
    _ = _ := by
      rw [List.drop_eq_getElem_cons h,e]
      rfl

private theorem gt_split {n : Nat} {i j : Fin n} (h : i<j) :
    gtLabels i (List.finRange n) =
      gtLabels i (before j) ++ (j :: gtLabels i (after j)) := by
  calc
    _ = gtLabels i (before j ++ (j :: after j)) := congrArg (gtLabels i) (fin_split j)
    _ = _ := by simp [gtLabels,h]

private theorem gt_after_self {n : Nat} (i : Fin n) :
    gtLabels i (after i) = after i := by
  apply List.filter_eq_self.mpr
  exact fun _ h => decide_eq_true (lt_after h)

private theorem gt_before_self {n : Nat} (i : Fin n) :
    gtLabels i (before i ++ [i]) = [] := by
  apply List.filter_eq_nil_iff.mpr
  intro x hx H
  have e := List.mem_append.mp hx
  rcases e with h | h
  · exact (Fin.lt_asymm (before_lt h)) (of_decide_eq_true H)
  · have ex := List.mem_singleton.mp h
    subst x
    exact (Fin.lt_irrefl _) (of_decide_eq_true H)

private theorem gt_range {n : Nat} (i : Fin n) : gtLabels i (List.finRange n) = after i := by
  have hs : List.finRange n = (before i ++ [i]) ++ after i := by
    rw [List.append_assoc,List.singleton_append]
    exact fin_split i
  calc
    _ = gtLabels i ((before i ++ [i]) ++ after i) := congrArg (gtLabels i) hs
    _ = gtLabels i (before i ++ [i]) ++ gtLabels i (after i) := by simp only [gtLabels,List.filter_append]
    _ = _ := by rw [gt_before_self,gt_after_self,List.nil_append]

private theorem between_length {n : Nat} {i j : Fin n} (h : i<j) :
    (gtLabels i (before j)).length = j.val-(i.val+1) := by
  have hi : i.val<j.val := h
  have hj := j.isLt
  have plen : (before i ++ [i]).length = i.val+1 := by simp [before_length]
  have hs : List.finRange n = (before i ++ [i]) ++ after i := by
    rw [List.append_assoc,List.singleton_append]
    exact fin_split i
  have cut : before j = (before i ++ [i]) ++ (after i).take (j.val-(i.val+1)) := by
    calc
      before j = (((before i ++ [i]) ++ after i).take j.val) :=
        congrArg (fun xs : List (Fin n) => xs.take j.val) hs
      _ = _ := by
        rw [List.take_append,List.take_of_length_le (by omega : (before i ++ [i]).length≤j.val),plen]
  have rightKeep : gtLabels i ((after i).take (j.val-(i.val+1))) =
      (after i).take (j.val-(i.val+1)) := by
    apply List.filter_eq_self.mpr
    exact fun _ hx => decide_eq_true (lt_after (List.mem_of_mem_take hx))
  have hc : gtLabels i (before j) = (after i).take (j.val-(i.val+1)) := by
    calc
      _ = gtLabels i ((before i ++ [i]) ++ (after i).take (j.val-(i.val+1))) :=
        congrArg (gtLabels i) cut
      _ = gtLabels i (before i ++ [i]) ++ gtLabels i ((after i).take (j.val-(i.val+1))) :=
        by simp only [gtLabels,List.filter_append]
      _ = _ := by rw [gt_before_self,rightKeep,List.nil_append]
  rw [hc,List.length_take,after_length]
  exact Nat.min_eq_left (by omega)

private def lastBlock {n : Nat} (a b : Fin n) : List (Key n) :=
  (gtLabels b (List.finRange n)).map (fun c => .sign a b c)

private def firstBlock {n : Nat} (a : Fin n) : List (Key n) :=
  (gtLabels a (List.finRange n)).flatMap (lastBlock a)

private def signTable (n : Nat) : List (Key n) :=
  (triples n).map (fun (a,b,c) => .sign a b c)

private theorem signTable_blocks (n : Nat) :
    signTable n = (List.finRange n).flatMap firstBlock := by
  unfold signTable triples pairs firstBlock lastBlock gtLabels
  simp only [List.map_flatMap,List.flatMap_assoc,List.flatMap_map,List.map_map,Function.comp_def]

def secondWeight {n : Nat} (b : Fin n) : Nat := n-(b.val+1)

/-- Number of subsequent ordered pairs after the first label a:
sum of suffix lengths n-b-1 over a<b<n (the triangular count). -/
def firstWeight {n : Nat} (a : Fin n) : Nat :=
  ((after a).map secondWeight).sum

private theorem lastBlock_length {n : Nat} (a b : Fin n) :
    (lastBlock a b).length = secondWeight b := by
  unfold lastBlock secondWeight
  rw [List.length_map,gt_range,after_length]

private theorem firstBlock_length {n : Nat} (a : Fin n) :
    (firstBlock a).length = firstWeight a := by
  unfold firstBlock firstWeight
  rw [gt_range,List.length_flatMap]
  simp only [lastBlock_length]

/-- One-based sign rank; no enumeration of triples, cap/cup constraints,
or full dictionary lookup is needed to evaluate this expression. -/
def rank {n : Nat} (a b c : Fin n) : Nat :=
  ((before a).map firstWeight).sum +
    ((gtLabels a (before b)).map secondWeight).sum +
    (c.val-(b.val+1)) + 1

private theorem idx_block {V : Type} [BEq V] [LawfulBEq V] {v : V}
    (l mid r : List V) (hL : v ∉ l) (hM : v ∈ mid) :
    (l ++ (mid ++ r)).idxOf v = l.length + mid.idxOf v := by
  rw [List.idxOf_append,ite_eq_right hL,List.idxOf_append,ite_eq_left hM,Nat.add_comm]

private theorem last_mem {n : Nat} {a b c : Fin n} (h : b<c) :
    EndpointVar.sign a b c ∈ lastBlock a b := by
  apply List.mem_map.mpr
  exact ⟨c,List.mem_filter.mpr ⟨List.mem_finRange c,decide_eq_true h⟩,rfl⟩

private theorem first_mem {n : Nat} {a b c : Fin n} (hab : a<b) (hbc : b<c) :
    EndpointVar.sign a b c ∈ firstBlock a := by
  exact List.mem_flatMap.mpr
    ⟨b,List.mem_filter.mpr ⟨List.mem_finRange b,decide_eq_true hab⟩,last_mem hbc⟩

private theorem idx_last {n : Nat} {a b c : Fin n} (hbc : b<c) :
    (lastBlock a b).idxOf (.sign a b c) = c.val-(b.val+1) := by
  have absent : EndpointVar.sign a b c ∉
      (gtLabels b (before c)).map (fun x => .sign a b x) := by
    intro hm
    obtain ⟨x,hx,e⟩ := List.mem_map.mp hm
    have hc : x=c := (EndpointVar.sign.inj e).2.2
    subst x
    exact Fin.lt_irrefl _ (before_lt (List.mem_filter.mp hx).1)
  unfold lastBlock
  rw [gt_split hbc,List.map_append,List.map_cons,List.idxOf_append,ite_eq_right absent,
      List.idxOf_cons_self,Nat.zero_add,List.length_map,between_length hbc]

private theorem idx_first {n : Nat} {a b c : Fin n} (hab : a<b) (hbc : b<c) :
    (firstBlock a).idxOf (.sign a b c) =
      ((gtLabels a (before b)).map secondWeight).sum + (c.val-(b.val+1)) := by
  have absent : EndpointVar.sign a b c ∉ (gtLabels a (before b)).flatMap (lastBlock a) := by
    intro hm
    obtain ⟨y,hy,hm⟩ := List.mem_flatMap.mp hm
    obtain ⟨z,_,e⟩ := List.mem_map.mp hm
    have hb : y=b := (EndpointVar.sign.inj e).2.1
    subst y
    exact Fin.lt_irrefl _ (before_lt (List.mem_filter.mp hy).1)
  unfold firstBlock
  rw [gt_split hab,List.flatMap_append,List.flatMap_cons,idx_block _ _ _ absent (last_mem hbc),
      List.length_flatMap,idx_last hbc]
  simp only [lastBlock_length]

private theorem idx_sign_table {n : Nat} {a b c : Fin n} (hab : a<b) (hbc : b<c) :
    (signTable n).idxOf (.sign a b c) =
      ((before a).map firstWeight).sum +
        (((gtLabels a (before b)).map secondWeight).sum + (c.val-(b.val+1))) := by
  have absent : EndpointVar.sign a b c ∉ (before a).flatMap firstBlock := by
    intro hm
    obtain ⟨x,hx,hm⟩ := List.mem_flatMap.mp hm
    obtain ⟨y,_,hm⟩ := List.mem_flatMap.mp hm
    obtain ⟨z,_,e⟩ := List.mem_map.mp hm
    have ha : x=a := (EndpointVar.sign.inj e).1
    subst x
    exact Fin.lt_irrefl _ (before_lt hx)
  have cut : signTable n =
      (before a).flatMap firstBlock ++
        (firstBlock a ++ (after a).flatMap firstBlock) := by
    rw [signTable_blocks,fin_split a,List.flatMap_append,List.flatMap_cons]
  rw [cut,idx_block _ _ _ absent (first_mem hab hbc),List.length_flatMap,idx_first hab hbc]
  simp only [firstBlock_length]

/-- Exact production rank for every ordered orientation triple, independent
of both cap/cup size parameters or any concrete 32-label reductions. -/
theorem production_sign_id {n A B : Nat} {a b c : Fin n}
    (hab : a<b) (hbc : b<c) :
    (dictionary n A B).idxOf (.sign a b c) + 1 = rank a b c := by
  have hm : EndpointVar.sign a b c ∈ signTable n := by
    rw [signTable_blocks]
    exact List.mem_flatMap.mpr ⟨a,List.mem_finRange a,first_mem hab hbc⟩
  change ((signTable n ++ sideDictionary n A .cap) ++ sideDictionary n B .cup).idxOf
    (.sign a b c) + 1 = _
  rw [List.append_assoc,List.idxOf_append,ite_eq_left hm,idx_sign_table hab hbc]
  unfold rank
  omega

set_option maxRecDepth 8192 in
/-- Small wired examples spanning both ends of the 32-label sign table. -/
theorem rank32_sanity :
    rank (0 : Fin 32) 1 2 = 1 ∧
    rank (0 : Fin 32) 2 3 = 31 ∧
    rank (1 : Fin 32) 2 3 = 466 ∧
    rank (29 : Fin 32) 30 31 = 4960 := by decide

#print axioms signTable_blocks
#print axioms between_length
#print axioms production_sign_id
#print axioms rank32_sanity

end ES33.EndpointConcrete.OrientationRank
