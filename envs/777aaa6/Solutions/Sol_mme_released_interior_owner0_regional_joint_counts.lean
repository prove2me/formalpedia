-- Prove2me | solution 1 for mme_released_interior_owner0_regional_joint_counts
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T04:13:29.139039+00:00
-- url     : https://prove2.me/submissions/ee3066f3-f004-4532-bdaa-dadf67b3b0de

import Definitions.Def_mme_released_interior_integer_profiles
open MME MME.ReleasedInterior

private theorem row_0_10 :
    reconstructed 0 10 =
      (ReleasedGlobal.jointRows 0 10).map (fun p => (p.1.val, p.2)) := by
  decide +kernel

private theorem row_0_11 :
    reconstructed 0 11 =
      (ReleasedGlobal.jointRows 0 11).map (fun p => (p.1.val, p.2)) := by
  decide +kernel

private theorem row_0_12 :
    reconstructed 0 12 =
      (ReleasedGlobal.jointRows 0 12).map (fun p => (p.1.val, p.2)) := by
  decide +kernel

private theorem row_0_13 :
    reconstructed 0 13 =
      (ReleasedGlobal.jointRows 0 13).map (fun p => (p.1.val, p.2)) := by
  decide +kernel

private theorem row_0_14 :
    reconstructed 0 14 =
      (ReleasedGlobal.jointRows 0 14).map (fun p => (p.1.val, p.2)) := by
  decide +kernel

private theorem row_0_15 :
    reconstructed 0 15 =
      (ReleasedGlobal.jointRows 0 15).map (fun p => (p.1.val, p.2)) := by
  decide +kernel

private theorem row_0_18 :
    reconstructed 0 18 =
      (ReleasedGlobal.jointRows 0 18).map (fun p => (p.1.val, p.2)) := by
  decide +kernel

private theorem row_0_19 :
    reconstructed 0 19 =
      (ReleasedGlobal.jointRows 0 19).map (fun p => (p.1.val, p.2)) := by
  decide +kernel

private theorem row_0_20 :
    reconstructed 0 20 =
      (ReleasedGlobal.jointRows 0 20).map (fun p => (p.1.val, p.2)) := by
  decide +kernel

private theorem row_0_21 :
    reconstructed 0 21 =
      (ReleasedGlobal.jointRows 0 21).map (fun p => (p.1.val, p.2)) := by
  decide +kernel

private theorem row_0_22 :
    reconstructed 0 22 =
      (ReleasedGlobal.jointRows 0 22).map (fun p => (p.1.val, p.2)) := by
  decide +kernel

private theorem row_0_25 :
    reconstructed 0 25 =
      (ReleasedGlobal.jointRows 0 25).map (fun p => (p.1.val, p.2)) := by
  decide +kernel

private theorem row_0_26 :
    reconstructed 0 26 =
      (ReleasedGlobal.jointRows 0 26).map (fun p => (p.1.val, p.2)) := by
  decide +kernel

private theorem row_0_27 :
    reconstructed 0 27 =
      (ReleasedGlobal.jointRows 0 27).map (fun p => (p.1.val, p.2)) := by
  decide +kernel

private theorem row_0_28 :
    reconstructed 0 28 =
      (ReleasedGlobal.jointRows 0 28).map (fun p => (p.1.val, p.2)) := by
  decide +kernel

private theorem row_0_31 :
    reconstructed 0 31 =
      (ReleasedGlobal.jointRows 0 31).map (fun p => (p.1.val, p.2)) := by
  decide +kernel

private theorem row_0_32 :
    reconstructed 0 32 =
      (ReleasedGlobal.jointRows 0 32).map (fun p => (p.1.val, p.2)) := by
  decide +kernel

private theorem row_0_33 :
    reconstructed 0 33 =
      (ReleasedGlobal.jointRows 0 33).map (fun p => (p.1.val, p.2)) := by
  decide +kernel

private theorem row_0_36 :
    reconstructed 0 36 =
      (ReleasedGlobal.jointRows 0 36).map (fun p => (p.1.val, p.2)) := by
  decide +kernel

private theorem row_0_37 :
    reconstructed 0 37 =
      (ReleasedGlobal.jointRows 0 37).map (fun p => (p.1.val, p.2)) := by
  decide +kernel

private theorem row_0_40 :
    reconstructed 0 40 =
      (ReleasedGlobal.jointRows 0 40).map (fun p => (p.1.val, p.2)) := by
  decide +kernel

theorem solution (s : Fin 45) :
    (seed 0 s).boundary = [] →
    reconstructed 0 s = (ReleasedGlobal.jointRows 0 s).map (fun p => (p.1.val, p.2)) := by
  fin_cases s
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact fun _ => row_0_10
  · exact fun _ => row_0_11
  · exact fun _ => row_0_12
  · exact fun _ => row_0_13
  · exact fun _ => row_0_14
  · exact fun _ => row_0_15
  · decide +kernel
  · decide +kernel
  · exact fun _ => row_0_18
  · exact fun _ => row_0_19
  · exact fun _ => row_0_20
  · exact fun _ => row_0_21
  · exact fun _ => row_0_22
  · decide +kernel
  · decide +kernel
  · exact fun _ => row_0_25
  · exact fun _ => row_0_26
  · exact fun _ => row_0_27
  · exact fun _ => row_0_28
  · decide +kernel
  · decide +kernel
  · exact fun _ => row_0_31
  · exact fun _ => row_0_32
  · exact fun _ => row_0_33
  · decide +kernel
  · decide +kernel
  · exact fun _ => row_0_36
  · exact fun _ => row_0_37
  · decide +kernel
  · decide +kernel
  · exact fun _ => row_0_40
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel

#print axioms solution
