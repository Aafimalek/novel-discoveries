import EulerC14IndexedPilot

namespace Euler.C14.IndexedDraft
set_option maxHeartbeats 1900000
set_option maxRecDepth 10000

theorem local_cnf_alignment : base = (List.range 135).map rowAt := rfl

theorem initialized : GoodBelow base rowAt 135 := by
  have hlen : base.length = 135 := rfl
  rw [← hlen]
  apply init
  intro j hj
  rw [hlen] at hj
  rw [local_cnf_alignment, List.getElem?_map, List.getElem?_range hj]
  rfl

theorem first24_fromExactLocalCNF : GoodBelow base rowAt 159 :=
  first24 initialized

#print axioms local_cnf_alignment
#print axioms first24_fromExactLocalCNF
end Euler.C14.IndexedDraft
