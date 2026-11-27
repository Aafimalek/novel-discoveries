import EulerAllUsedDiagramData

namespace EulerAllUsedDiagrams

def allowedOutput (input : List (List Nat)) : Bool :=
  !oneOverlap (ofColumns input) || published.contains (canonical (ofColumns input))

def tailChoices (a b : List Nat) : List (List (List Nat)) :=
  patterns.flatMap fun c => patterns.map fun d => [a,b,c,d]

def shard (a b : List Nat) : Bool := (tailChoices a b).all allowedOutput

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem shard00 : shard [1, 1, 1] [1, 1, 1] = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem shard01 : shard [1, 1, 1] [1, 1, 2] = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem shard02 : shard [1, 1, 1] [1, 2, 1] = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem shard03 : shard [1, 1, 1] [1, 2, 2] = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem shard04 : shard [1, 1, 1] [1, 2, 3] = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem shard10 : shard [1, 1, 2] [1, 1, 1] = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem shard11 : shard [1, 1, 2] [1, 1, 2] = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem shard12 : shard [1, 1, 2] [1, 2, 1] = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem shard13 : shard [1, 1, 2] [1, 2, 2] = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem shard14 : shard [1, 1, 2] [1, 2, 3] = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem shard20 : shard [1, 2, 1] [1, 1, 1] = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem shard21 : shard [1, 2, 1] [1, 1, 2] = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem shard22 : shard [1, 2, 1] [1, 2, 1] = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem shard23 : shard [1, 2, 1] [1, 2, 2] = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem shard24 : shard [1, 2, 1] [1, 2, 3] = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem shard30 : shard [1, 2, 2] [1, 1, 1] = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem shard31 : shard [1, 2, 2] [1, 1, 2] = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem shard32 : shard [1, 2, 2] [1, 2, 1] = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem shard33 : shard [1, 2, 2] [1, 2, 2] = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem shard34 : shard [1, 2, 2] [1, 2, 3] = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem shard40 : shard [1, 2, 3] [1, 1, 1] = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem shard41 : shard [1, 2, 3] [1, 1, 2] = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem shard42 : shard [1, 2, 3] [1, 2, 1] = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem shard43 : shard [1, 2, 3] [1, 2, 2] = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem shard44 : shard [1, 2, 3] [1, 2, 3] = true := by decide +kernel

theorem validInput_is_published (a b c d : List Nat)
    (ha : a ∈ patterns) (hb : b ∈ patterns) (hc : c ∈ patterns) (hd : d ∈ patterns)
    (overlap : oneOverlap (ofColumns [a,b,c,d]) = true) :
    canonical (ofColumns [a,b,c,d]) ∈ published := by
  have hs : shard a b = true := by
    simp only [patterns, List.mem_cons, List.mem_nil_iff, or_false] at ha hb
    rcases ha with rfl | rfl | rfl | rfl | rfl <;>
      rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact shard00
    · exact shard01
    · exact shard02
    · exact shard03
    · exact shard04
    · exact shard10
    · exact shard11
    · exact shard12
    · exact shard13
    · exact shard14
    · exact shard20
    · exact shard21
    · exact shard22
    · exact shard23
    · exact shard24
    · exact shard30
    · exact shard31
    · exact shard32
    · exact shard33
    · exact shard34
    · exact shard40
    · exact shard41
    · exact shard42
    · exact shard43
    · exact shard44

  have hin : [a,b,c,d] ∈ tailChoices a b :=
    List.mem_flatMap.mpr ⟨c,hc,List.mem_map.mpr ⟨d,hd,rfl⟩⟩
  have hgood := List.all_eq_true.mp hs _ hin
  simpa [allowedOutput,overlap] using hgood

#print axioms validInput_is_published
end EulerAllUsedDiagrams
