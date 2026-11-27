import RotationArithmetic

namespace CertifiedG449Rotation

set_option maxRecDepth 32768
set_option maxHeartbeats 160000000

theorem checked_exact_pair_table : orientedPairs = publishedPairs := by decide +kernel

theorem checked_inverse_rotation :
    (List.range 449).all permOK = true := by decide +kernel

theorem checked_center : center < 449 ∧ rot center = center := by decide +kernel

theorem checked_ring_labels :
    ring.length = 7 ∧ ring.Nodup ∧ (ring.all (fun a => decide (a < 449))) = true := by
  decide +kernel

theorem checked_neighbors : (List.range 449).all centerMembershipOK = true := by
  decide +kernel

theorem checked_neighbor_cycle : (List.range 7).all cyclicOK = true := by
  decide +kernel

theorem checked_neighbor_independence : independenceOK = true := by
  decide +kernel

#print axioms checked_exact_pair_table
#print axioms checked_inverse_rotation
#print axioms checked_center
#print axioms checked_ring_labels
#print axioms checked_neighbors
#print axioms checked_neighbor_cycle
#print axioms checked_neighbor_independence

end CertifiedG449Rotation
