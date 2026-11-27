import RotationArithmetic

namespace CertifiedG449Rotation

open G449OrbitArithmetic
set_option maxRecDepth 32768
set_option maxHeartbeats 160000000

private theorem geom0 : (List.range 40).all (fun j => geomOK (0+j)) = true := by
  decide +kernel

private theorem geom40 : (List.range 40).all (fun j => geomOK (40+j)) = true := by
  decide +kernel

private theorem geom80 : (List.range 40).all (fun j => geomOK (80+j)) = true := by
  decide +kernel

private theorem geom120 : (List.range 40).all (fun j => geomOK (120+j)) = true := by
  decide +kernel

private theorem geom160 : (List.range 40).all (fun j => geomOK (160+j)) = true := by
  decide +kernel

private theorem geom200 : (List.range 40).all (fun j => geomOK (200+j)) = true := by
  decide +kernel

private theorem geom240 : (List.range 40).all (fun j => geomOK (240+j)) = true := by
  decide +kernel

private theorem geom280 : (List.range 40).all (fun j => geomOK (280+j)) = true := by
  decide +kernel

private theorem geom320 : (List.range 40).all (fun j => geomOK (320+j)) = true := by
  decide +kernel

private theorem geom360 : (List.range 40).all (fun j => geomOK (360+j)) = true := by
  decide +kernel

private theorem geom400 : (List.range 40).all (fun j => geomOK (400+j)) = true := by
  decide +kernel

private theorem geom440 : (List.range 9).all (fun j => geomOK (440+j)) = true := by
  decide +kernel

theorem G449_rotation_coordinates (k : Nat) (hk : k < 449) (i : Nat) (hi : i < 12) :
    (vertices (rot k)).coeffs.getD i 0 =
      spin (fun j => (vertices k).coeffs.getD j 0) i := by
  suffices h : geomOK k = true from
    beq_iff_eq.mp (List.all_eq_true.mp h i (List.mem_range.mpr hi))
  by_cases a0 : k < 40
  · have e := List.all_eq_true.mp geom0 (k-0) (List.mem_range.mpr (by omega))
    rwa [show 0+(k-0)=k by omega] at e
  by_cases a40 : k < 80
  · have e := List.all_eq_true.mp geom40 (k-40) (List.mem_range.mpr (by omega))
    rwa [show 40+(k-40)=k by omega] at e
  by_cases a80 : k < 120
  · have e := List.all_eq_true.mp geom80 (k-80) (List.mem_range.mpr (by omega))
    rwa [show 80+(k-80)=k by omega] at e
  by_cases a120 : k < 160
  · have e := List.all_eq_true.mp geom120 (k-120) (List.mem_range.mpr (by omega))
    rwa [show 120+(k-120)=k by omega] at e
  by_cases a160 : k < 200
  · have e := List.all_eq_true.mp geom160 (k-160) (List.mem_range.mpr (by omega))
    rwa [show 160+(k-160)=k by omega] at e
  by_cases a200 : k < 240
  · have e := List.all_eq_true.mp geom200 (k-200) (List.mem_range.mpr (by omega))
    rwa [show 200+(k-200)=k by omega] at e
  by_cases a240 : k < 280
  · have e := List.all_eq_true.mp geom240 (k-240) (List.mem_range.mpr (by omega))
    rwa [show 240+(k-240)=k by omega] at e
  by_cases a280 : k < 320
  · have e := List.all_eq_true.mp geom280 (k-280) (List.mem_range.mpr (by omega))
    rwa [show 280+(k-280)=k by omega] at e
  by_cases a320 : k < 360
  · have e := List.all_eq_true.mp geom320 (k-320) (List.mem_range.mpr (by omega))
    rwa [show 320+(k-320)=k by omega] at e
  by_cases a360 : k < 400
  · have e := List.all_eq_true.mp geom360 (k-360) (List.mem_range.mpr (by omega))
    rwa [show 360+(k-360)=k by omega] at e
  by_cases a400 : k < 440
  · have e := List.all_eq_true.mp geom400 (k-400) (List.mem_range.mpr (by omega))
    rwa [show 400+(k-400)=k by omega] at e
  by_cases a440 : k < 449
  · have e := List.all_eq_true.mp geom440 (k-440) (List.mem_range.mpr (by omega))
    rwa [show 440+(k-440)=k by omega] at e
  omega

#print axioms G449_rotation_coordinates
end CertifiedG449Rotation
