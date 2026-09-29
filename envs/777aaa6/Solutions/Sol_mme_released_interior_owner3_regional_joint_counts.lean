-- Prove2me | solution 1 for mme_released_interior_owner3_regional_joint_counts
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T04:14:29.195883+00:00
-- url     : https://prove2.me/submissions/c73ad315-3ca6-4f31-85c6-28e7927fd2b1

import Definitions.Def_mme_released_interior_integer_profiles
open MME MME.ReleasedInterior

private theorem row_3_10 :
    reconstructed 3 10 =
      (ReleasedGlobal.jointRows 3 10).map (fun p => (p.1.val, p.2)) := by
  decide +kernel

private theorem row_3_11 :
    reconstructed 3 11 =
      (ReleasedGlobal.jointRows 3 11).map (fun p => (p.1.val, p.2)) := by
  decide +kernel

private theorem row_3_12 :
    reconstructed 3 12 =
      (ReleasedGlobal.jointRows 3 12).map (fun p => (p.1.val, p.2)) := by
  decide +kernel

private theorem row_3_13 :
    reconstructed 3 13 =
      (ReleasedGlobal.jointRows 3 13).map (fun p => (p.1.val, p.2)) := by
  decide +kernel

private theorem row_3_14 :
    reconstructed 3 14 =
      (ReleasedGlobal.jointRows 3 14).map (fun p => (p.1.val, p.2)) := by
  decide +kernel

private theorem row_3_15 :
    reconstructed 3 15 =
      (ReleasedGlobal.jointRows 3 15).map (fun p => (p.1.val, p.2)) := by
  decide +kernel

private theorem row_3_18 :
    reconstructed 3 18 =
      (ReleasedGlobal.jointRows 3 18).map (fun p => (p.1.val, p.2)) := by
  decide +kernel

private theorem row_3_19 :
    reconstructed 3 19 =
      (ReleasedGlobal.jointRows 3 19).map (fun p => (p.1.val, p.2)) := by
  decide +kernel

private theorem row_3_20 :
    reconstructed 3 20 =
      (ReleasedGlobal.jointRows 3 20).map (fun p => (p.1.val, p.2)) := by
  decide +kernel

private theorem row_3_21 :
    reconstructed 3 21 =
      (ReleasedGlobal.jointRows 3 21).map (fun p => (p.1.val, p.2)) := by
  decide +kernel

private theorem row_3_22 :
    reconstructed 3 22 =
      (ReleasedGlobal.jointRows 3 22).map (fun p => (p.1.val, p.2)) := by
  decide +kernel

private theorem row_3_25 :
    reconstructed 3 25 =
      (ReleasedGlobal.jointRows 3 25).map (fun p => (p.1.val, p.2)) := by
  decide +kernel

private theorem row_3_26 :
    reconstructed 3 26 =
      (ReleasedGlobal.jointRows 3 26).map (fun p => (p.1.val, p.2)) := by
  decide +kernel

private theorem row_3_27 :
    reconstructed 3 27 =
      (ReleasedGlobal.jointRows 3 27).map (fun p => (p.1.val, p.2)) := by
  decide +kernel

private theorem row_3_28 :
    reconstructed 3 28 =
      (ReleasedGlobal.jointRows 3 28).map (fun p => (p.1.val, p.2)) := by
  decide +kernel

private theorem row_3_31 :
    reconstructed 3 31 =
      (ReleasedGlobal.jointRows 3 31).map (fun p => (p.1.val, p.2)) := by
  decide +kernel

private theorem row_3_32 :
    reconstructed 3 32 =
      (ReleasedGlobal.jointRows 3 32).map (fun p => (p.1.val, p.2)) := by
  decide +kernel

private theorem row_3_33 :
    reconstructed 3 33 =
      (ReleasedGlobal.jointRows 3 33).map (fun p => (p.1.val, p.2)) := by
  decide +kernel

private theorem row_3_36 :
    reconstructed 3 36 =
      (ReleasedGlobal.jointRows 3 36).map (fun p => (p.1.val, p.2)) := by
  decide +kernel

private theorem row_3_37 :
    reconstructed 3 37 =
      (ReleasedGlobal.jointRows 3 37).map (fun p => (p.1.val, p.2)) := by
  decide +kernel

private theorem row_3_40 :
    reconstructed 3 40 =
      (ReleasedGlobal.jointRows 3 40).map (fun p => (p.1.val, p.2)) := by
  decide +kernel

theorem solution (s : Fin 45) :
    (seed 3 s).boundary = [] →
    reconstructed 3 s = (ReleasedGlobal.jointRows 3 s).map (fun p => (p.1.val, p.2)) := by
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
  · exact fun _ => row_3_10
  · exact fun _ => row_3_11
  · exact fun _ => row_3_12
  · exact fun _ => row_3_13
  · exact fun _ => row_3_14
  · exact fun _ => row_3_15
  · decide +kernel
  · decide +kernel
  · exact fun _ => row_3_18
  · exact fun _ => row_3_19
  · exact fun _ => row_3_20
  · exact fun _ => row_3_21
  · exact fun _ => row_3_22
  · decide +kernel
  · decide +kernel
  · exact fun _ => row_3_25
  · exact fun _ => row_3_26
  · exact fun _ => row_3_27
  · exact fun _ => row_3_28
  · decide +kernel
  · decide +kernel
  · exact fun _ => row_3_31
  · exact fun _ => row_3_32
  · exact fun _ => row_3_33
  · decide +kernel
  · decide +kernel
  · exact fun _ => row_3_36
  · exact fun _ => row_3_37
  · decide +kernel
  · decide +kernel
  · exact fun _ => row_3_40
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel

#print axioms solution
