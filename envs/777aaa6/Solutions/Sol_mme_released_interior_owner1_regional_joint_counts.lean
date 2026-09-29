-- Prove2me | solution 1 for mme_released_interior_owner1_regional_joint_counts
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T04:14:28.046753+00:00
-- url     : https://prove2.me/submissions/9e467019-c77a-4a66-881b-4643c6265169

import Definitions.Def_mme_released_interior_integer_profiles
open MME MME.ReleasedInterior

private theorem row_1_10 :
    reconstructed 1 10 =
      (ReleasedGlobal.jointRows 1 10).map (fun p => (p.1.val, p.2)) := by
  decide +kernel

private theorem row_1_11 :
    reconstructed 1 11 =
      (ReleasedGlobal.jointRows 1 11).map (fun p => (p.1.val, p.2)) := by
  decide +kernel

private theorem row_1_12 :
    reconstructed 1 12 =
      (ReleasedGlobal.jointRows 1 12).map (fun p => (p.1.val, p.2)) := by
  decide +kernel

private theorem row_1_13 :
    reconstructed 1 13 =
      (ReleasedGlobal.jointRows 1 13).map (fun p => (p.1.val, p.2)) := by
  decide +kernel

private theorem row_1_14 :
    reconstructed 1 14 =
      (ReleasedGlobal.jointRows 1 14).map (fun p => (p.1.val, p.2)) := by
  decide +kernel

private theorem row_1_15 :
    reconstructed 1 15 =
      (ReleasedGlobal.jointRows 1 15).map (fun p => (p.1.val, p.2)) := by
  decide +kernel

private theorem row_1_18 :
    reconstructed 1 18 =
      (ReleasedGlobal.jointRows 1 18).map (fun p => (p.1.val, p.2)) := by
  decide +kernel

private theorem row_1_19 :
    reconstructed 1 19 =
      (ReleasedGlobal.jointRows 1 19).map (fun p => (p.1.val, p.2)) := by
  decide +kernel

private theorem row_1_20 :
    reconstructed 1 20 =
      (ReleasedGlobal.jointRows 1 20).map (fun p => (p.1.val, p.2)) := by
  decide +kernel

private theorem row_1_21 :
    reconstructed 1 21 =
      (ReleasedGlobal.jointRows 1 21).map (fun p => (p.1.val, p.2)) := by
  decide +kernel

private theorem row_1_22 :
    reconstructed 1 22 =
      (ReleasedGlobal.jointRows 1 22).map (fun p => (p.1.val, p.2)) := by
  decide +kernel

private theorem row_1_25 :
    reconstructed 1 25 =
      (ReleasedGlobal.jointRows 1 25).map (fun p => (p.1.val, p.2)) := by
  decide +kernel

private theorem row_1_26 :
    reconstructed 1 26 =
      (ReleasedGlobal.jointRows 1 26).map (fun p => (p.1.val, p.2)) := by
  decide +kernel

private theorem row_1_27 :
    reconstructed 1 27 =
      (ReleasedGlobal.jointRows 1 27).map (fun p => (p.1.val, p.2)) := by
  decide +kernel

private theorem row_1_28 :
    reconstructed 1 28 =
      (ReleasedGlobal.jointRows 1 28).map (fun p => (p.1.val, p.2)) := by
  decide +kernel

private theorem row_1_31 :
    reconstructed 1 31 =
      (ReleasedGlobal.jointRows 1 31).map (fun p => (p.1.val, p.2)) := by
  decide +kernel

private theorem row_1_32 :
    reconstructed 1 32 =
      (ReleasedGlobal.jointRows 1 32).map (fun p => (p.1.val, p.2)) := by
  decide +kernel

private theorem row_1_33 :
    reconstructed 1 33 =
      (ReleasedGlobal.jointRows 1 33).map (fun p => (p.1.val, p.2)) := by
  decide +kernel

private theorem row_1_36 :
    reconstructed 1 36 =
      (ReleasedGlobal.jointRows 1 36).map (fun p => (p.1.val, p.2)) := by
  decide +kernel

private theorem row_1_37 :
    reconstructed 1 37 =
      (ReleasedGlobal.jointRows 1 37).map (fun p => (p.1.val, p.2)) := by
  decide +kernel

private theorem row_1_40 :
    reconstructed 1 40 =
      (ReleasedGlobal.jointRows 1 40).map (fun p => (p.1.val, p.2)) := by
  decide +kernel

theorem solution (s : Fin 45) :
    (seed 1 s).boundary = [] →
    reconstructed 1 s = (ReleasedGlobal.jointRows 1 s).map (fun p => (p.1.val, p.2)) := by
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
  · exact fun _ => row_1_10
  · exact fun _ => row_1_11
  · exact fun _ => row_1_12
  · exact fun _ => row_1_13
  · exact fun _ => row_1_14
  · exact fun _ => row_1_15
  · decide +kernel
  · decide +kernel
  · exact fun _ => row_1_18
  · exact fun _ => row_1_19
  · exact fun _ => row_1_20
  · exact fun _ => row_1_21
  · exact fun _ => row_1_22
  · decide +kernel
  · decide +kernel
  · exact fun _ => row_1_25
  · exact fun _ => row_1_26
  · exact fun _ => row_1_27
  · exact fun _ => row_1_28
  · decide +kernel
  · decide +kernel
  · exact fun _ => row_1_31
  · exact fun _ => row_1_32
  · exact fun _ => row_1_33
  · decide +kernel
  · decide +kernel
  · exact fun _ => row_1_36
  · exact fun _ => row_1_37
  · decide +kernel
  · decide +kernel
  · exact fun _ => row_1_40
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel

#print axioms solution
