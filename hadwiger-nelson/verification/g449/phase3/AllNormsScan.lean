import DirBlock0
import DirBlock1
import DirBlock2
import DirBlock3
import DirBlock4
import DirBlock5
import DirBlock6

namespace G449OrbitArithmetic

theorem all_norms_scan (k : Nat) (hk : k < 49) :
    testNorm powers (dirs k) = true := by
  by_cases z0 : k < 7
  · have h := List.all_eq_true.mp dir_block_0 (k-0) (List.mem_range.mpr (by omega))
    rwa [show 0+(k-0)=k by omega] at h
  by_cases z1 : k < 14
  · have h := List.all_eq_true.mp dir_block_1 (k-7) (List.mem_range.mpr (by omega))
    rwa [show 7+(k-7)=k by omega] at h
  by_cases z2 : k < 21
  · have h := List.all_eq_true.mp dir_block_2 (k-14) (List.mem_range.mpr (by omega))
    rwa [show 14+(k-14)=k by omega] at h
  by_cases z3 : k < 28
  · have h := List.all_eq_true.mp dir_block_3 (k-21) (List.mem_range.mpr (by omega))
    rwa [show 21+(k-21)=k by omega] at h
  by_cases z4 : k < 35
  · have h := List.all_eq_true.mp dir_block_4 (k-28) (List.mem_range.mpr (by omega))
    rwa [show 28+(k-28)=k by omega] at h
  by_cases z5 : k < 42
  · have h := List.all_eq_true.mp dir_block_5 (k-35) (List.mem_range.mpr (by omega))
    rwa [show 35+(k-35)=k by omega] at h
  by_cases z6 : k < 49
  · have h := List.all_eq_true.mp dir_block_6 (k-42) (List.mem_range.mpr (by omega))
    rwa [show 42+(k-42)=k by omega] at h

  omega

#print axioms all_norms_scan
end G449OrbitArithmetic
