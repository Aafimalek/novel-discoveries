/- Static draft: actual production numbering and clause containment. -/
import ActualCoverage
import PacketTextPilot

namespace ES33.EndpointConcrete

open ES33.Numbering

private def signTable32 : List (Key 32) :=
  (triples 32).map (fun (a,b,c) => .sign a b c)

private def signPrefix : List (Key 32) := signTable32.take 466

private def sideTail32 : List (Key 32) :=
  sideDictionary 32 7 .cap ++ sideDictionary 32 6 .cup

private theorem append_cut {V : Type} (d t : List V) (k : Nat) :
    d ++ t = d.take k ++ (d.drop k ++ t) := by
  calc
    d ++ t = (d.take k ++ d.drop k) ++ t :=
      congrArg (fun xs : List V => xs ++ t) (List.take_append_drop k d).symm
    _ = _ := List.append_assoc _ _ _

private theorem dict_split :
    dictionary 32 7 6 = signPrefix ++ (signTable32.drop 466 ++ sideTail32) := by
  change (signTable32 ++ sideDictionary 32 7 .cap) ++ sideDictionary 32 6 .cup = _
  calc
    _ = signTable32 ++ sideTail32 := List.append_assoc _ _ _
    _ = _ := append_cut signTable32 sideTail32 466

def productionId32 (v : Key 32) : Nat := (dictionary 32 7 6).idxOf v + 1

-- Four concrete computations stop at the actual first 466 sign entries;
-- neither side dictionary nor any complete numbered row block is evaluated.
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
private theorem prefix_length : signPrefix.length = 466 := by decide

private theorem id_of_prefix {v : Key 32} {i : Nat}
    (hi : signPrefix.idxOf v + 1 = i) (hb : i≤466) : productionId32 v = i := by
  have hlen := prefix_length
  have hm : v ∈ signPrefix := List.idxOf_lt_length_iff.mp (by omega)
  unfold productionId32
  rw [dict_split,List.idxOf_append,ite_eq_left hm]
  exact hi

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem production_id_012 : productionId32 (.sign 0 1 2) = 1 :=
  id_of_prefix (by decide) (by decide)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem production_id_013 : productionId32 (.sign 0 1 3) = 2 :=
  id_of_prefix (by decide) (by decide)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem production_id_023 : productionId32 (.sign 0 2 3) = 31 :=
  id_of_prefix (by decide) (by decide)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem production_id_123 : productionId32 (.sign 1 2 3) = 466 :=
  id_of_prefix (by decide) (by decide)

def firstPacketTyped : CNF (Key 32) := packetRows (0 : Fin 32) 1 2 3

theorem internal_packet_exact :
    encode productionId32 firstPacketTyped = ES33.ExternalPacketPilot.expected := by
  simp [encode,firstPacketTyped,packetRows,signed,flip,sign,
    production_id_012,production_id_013,production_id_023,production_id_123,
    ES33.ExternalPacketPilot.expected]

private theorem first_packet_in : ((0 : Fin 32),1,2,3) ∈ packets 32 := by
  unfold packets
  exact List.mem_flatMap.mpr ⟨((0 : Fin 32),1,2),
    triples_contains (by decide) (by decide),
    List.mem_map.mpr ⟨(3 : Fin 32),
      List.mem_filter.mpr ⟨List.mem_finRange _,by decide⟩,rfl⟩⟩

private theorem first_packet_row {c : List (Cell 32)} (hc : c ∈ firstPacketTyped) :
    c ∈ typedRows 32 7 7 6 := by
  simp only [typedRows,List.mem_append,or_assoc]
  exact Or.inr (Or.inr (Or.inr (List.mem_flatMap.mpr
    ⟨((0 : Fin 32),1,2,3),first_packet_in,hc⟩)))

private theorem compiled_row_mem {V : Type} [BEq V] (keys : List V)
    (F : CNF V) (supports : Supports keys F) {c : List (Lit V)} (hc : c ∈ F) :
    c.map (signed (fun v => keys.idxOf v+1)) ∈ compile keys F supports := by
  unfold compile encode
  refine List.mem_map.mpr ⟨scopeClause keys c (supports c hc),?_,?_⟩
  · unfold scope
    exact List.mem_map.mpr ⟨⟨c,hc⟩,List.mem_attach F _,rfl⟩
  · unfold scopeClause
    rw [List.map_map]
    exact List.attach_map_val (l := c) (f := signed (fun v => keys.idxOf v+1))

/-- This is exact clause membership in the actual internally compiled
target, not an equality of full files or a claim about the global row offset. -/
theorem external_packet_is_internal
    {C : NumberedCNF}
    (parsed : ES33.ExternalPacketPilot.parseBodyChunk 37365 6
      ES33.ExternalPacketPilot.body = some C) :
    C = encode productionId32 firstPacketTyped ∧
    ∀ c ∈ C, c ∈ compile (dictionary 32 7 6) (typedRows 32 7 7 6) target32_covered := by
  have hC : C = encode productionId32 firstPacketTyped :=
    (Option.some.inj (parsed.symm.trans ES33.ExternalPacketPilot.parsed_body)).trans
      internal_packet_exact.symm
  refine ⟨hC,?_⟩
  rw [hC]
  intro c hc
  obtain ⟨row,hr,rfl⟩ := List.mem_map.mp hc
  exact compiled_row_mem (dictionary 32 7 6) (typedRows 32 7 7 6)
    target32_covered (first_packet_row hr)

/-- Closed six-row checkpoint: the embedded bytes parse and each exact
signed row occurs in the real compiled formula. -/
theorem parsed_packet_mem_internal :
    ES33.ExternalPacketPilot.parseBodyChunk 37365 6 ES33.ExternalPacketPilot.body =
      some (encode productionId32 firstPacketTyped) ∧
    ∀ c ∈ encode productionId32 firstPacketTyped,
      c ∈ compile (dictionary 32 7 6) (typedRows 32 7 7 6) target32_covered := by
  obtain ⟨h,mem⟩ := external_packet_is_internal ES33.ExternalPacketPilot.parsed_body
  rw [h] at mem
  exact ⟨ES33.ExternalPacketPilot.parsed_body.trans (congrArg some h),mem⟩

#print axioms production_id_012
#print axioms production_id_013
#print axioms production_id_023
#print axioms production_id_123
#print axioms internal_packet_exact
#print axioms external_packet_is_internal
#print axioms parsed_packet_mem_internal

end ES33.EndpointConcrete
