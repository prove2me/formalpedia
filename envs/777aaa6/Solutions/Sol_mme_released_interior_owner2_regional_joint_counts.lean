-- Prove2me | solution 1 for mme_released_interior_owner2_regional_joint_counts
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T04:13:30.053453+00:00
-- url     : https://prove2.me/submissions/511badac-19f9-466c-9d82-72370dad89f6

import Definitions.Def_mme_released_interior_integer_profiles
open MME MME.ReleasedInterior

private theorem row_2_10 :
    reconstructed 2 10 =
      (ReleasedGlobal.jointRows 2 10).map (fun p => (p.1.val, p.2)) := by
  decide +kernel

private theorem row_2_11 :
    reconstructed 2 11 =
      (ReleasedGlobal.jointRows 2 11).map (fun p => (p.1.val, p.2)) := by
  decide +kernel

private theorem row_2_12 :
    reconstructed 2 12 =
      (ReleasedGlobal.jointRows 2 12).map (fun p => (p.1.val, p.2)) := by
  decide +kernel

private theorem row_2_13 :
    reconstructed 2 13 =
      (ReleasedGlobal.jointRows 2 13).map (fun p => (p.1.val, p.2)) := by
  decide +kernel

private theorem row_2_14 :
    reconstructed 2 14 =
      (ReleasedGlobal.jointRows 2 14).map (fun p => (p.1.val, p.2)) := by
  decide +kernel

private theorem row_2_15 :
    reconstructed 2 15 =
      (ReleasedGlobal.jointRows 2 15).map (fun p => (p.1.val, p.2)) := by
  decide +kernel

private theorem row_2_18 :
    reconstructed 2 18 =
      (ReleasedGlobal.jointRows 2 18).map (fun p => (p.1.val, p.2)) := by
  decide +kernel

private theorem row_2_19 :
    reconstructed 2 19 =
      (ReleasedGlobal.jointRows 2 19).map (fun p => (p.1.val, p.2)) := by
  decide +kernel

private theorem row_2_20 :
    reconstructed 2 20 =
      (ReleasedGlobal.jointRows 2 20).map (fun p => (p.1.val, p.2)) := by
  decide +kernel

private theorem row_2_21 :
    reconstructed 2 21 =
      (ReleasedGlobal.jointRows 2 21).map (fun p => (p.1.val, p.2)) := by
  decide +kernel

private theorem row_2_22 :
    reconstructed 2 22 =
      (ReleasedGlobal.jointRows 2 22).map (fun p => (p.1.val, p.2)) := by
  decide +kernel

private theorem row_2_25 :
    reconstructed 2 25 =
      (ReleasedGlobal.jointRows 2 25).map (fun p => (p.1.val, p.2)) := by
  decide +kernel

private theorem row_2_26 :
    reconstructed 2 26 =
      (ReleasedGlobal.jointRows 2 26).map (fun p => (p.1.val, p.2)) := by
  decide +kernel

private theorem row_2_27 :
    reconstructed 2 27 =
      (ReleasedGlobal.jointRows 2 27).map (fun p => (p.1.val, p.2)) := by
  decide +kernel

private theorem row_2_28 :
    reconstructed 2 28 =
      (ReleasedGlobal.jointRows 2 28).map (fun p => (p.1.val, p.2)) := by
  decide +kernel

private theorem row_2_31 :
    reconstructed 2 31 =
      (ReleasedGlobal.jointRows 2 31).map (fun p => (p.1.val, p.2)) := by
  decide +kernel

private theorem row_2_32 :
    reconstructed 2 32 =
      (ReleasedGlobal.jointRows 2 32).map (fun p => (p.1.val, p.2)) := by
  decide +kernel

private theorem row_2_33 :
    reconstructed 2 33 =
      (ReleasedGlobal.jointRows 2 33).map (fun p => (p.1.val, p.2)) := by
  decide +kernel

private theorem row_2_36 :
    reconstructed 2 36 =
      (ReleasedGlobal.jointRows 2 36).map (fun p => (p.1.val, p.2)) := by
  decide +kernel

private theorem row_2_37 :
    reconstructed 2 37 =
      (ReleasedGlobal.jointRows 2 37).map (fun p => (p.1.val, p.2)) := by
  decide +kernel

private theorem row_2_40 :
    reconstructed 2 40 =
      (ReleasedGlobal.jointRows 2 40).map (fun p => (p.1.val, p.2)) := by
  decide +kernel

theorem solution (s : Fin 45) :
    (seed 2 s).boundary = [] →
    reconstructed 2 s = (ReleasedGlobal.jointRows 2 s).map (fun p => (p.1.val, p.2)) := by
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
  · exact fun _ => row_2_10
  · exact fun _ => row_2_11
  · exact fun _ => row_2_12
  · exact fun _ => row_2_13
  · exact fun _ => row_2_14
  · exact fun _ => row_2_15
  · decide +kernel
  · decide +kernel
  · exact fun _ => row_2_18
  · exact fun _ => row_2_19
  · exact fun _ => row_2_20
  · exact fun _ => row_2_21
  · exact fun _ => row_2_22
  · decide +kernel
  · decide +kernel
  · exact fun _ => row_2_25
  · exact fun _ => row_2_26
  · exact fun _ => row_2_27
  · exact fun _ => row_2_28
  · decide +kernel
  · decide +kernel
  · exact fun _ => row_2_31
  · exact fun _ => row_2_32
  · exact fun _ => row_2_33
  · decide +kernel
  · decide +kernel
  · exact fun _ => row_2_36
  · exact fun _ => row_2_37
  · decide +kernel
  · decide +kernel
  · exact fun _ => row_2_40
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel

#print axioms solution
