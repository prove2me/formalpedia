-- Prove2me | solution 1 for mme_released_interior_owner5_regional_joint_counts
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T04:15:34.05369+00:00
-- url     : https://prove2.me/submissions/bff5be16-ab28-4784-8082-1a736226d299

import Definitions.Def_mme_released_interior_integer_profiles
open MME MME.ReleasedInterior

private theorem row_5_10 :
    reconstructed 5 10 =
      (ReleasedGlobal.jointRows 5 10).map (fun p => (p.1.val, p.2)) := by
  decide +kernel

private theorem row_5_11 :
    reconstructed 5 11 =
      (ReleasedGlobal.jointRows 5 11).map (fun p => (p.1.val, p.2)) := by
  decide +kernel

private theorem row_5_12 :
    reconstructed 5 12 =
      (ReleasedGlobal.jointRows 5 12).map (fun p => (p.1.val, p.2)) := by
  decide +kernel

private theorem row_5_13 :
    reconstructed 5 13 =
      (ReleasedGlobal.jointRows 5 13).map (fun p => (p.1.val, p.2)) := by
  decide +kernel

private theorem row_5_14 :
    reconstructed 5 14 =
      (ReleasedGlobal.jointRows 5 14).map (fun p => (p.1.val, p.2)) := by
  decide +kernel

private theorem row_5_15 :
    reconstructed 5 15 =
      (ReleasedGlobal.jointRows 5 15).map (fun p => (p.1.val, p.2)) := by
  decide +kernel

private theorem row_5_18 :
    reconstructed 5 18 =
      (ReleasedGlobal.jointRows 5 18).map (fun p => (p.1.val, p.2)) := by
  decide +kernel

private theorem row_5_19 :
    reconstructed 5 19 =
      (ReleasedGlobal.jointRows 5 19).map (fun p => (p.1.val, p.2)) := by
  decide +kernel

private theorem row_5_20 :
    reconstructed 5 20 =
      (ReleasedGlobal.jointRows 5 20).map (fun p => (p.1.val, p.2)) := by
  decide +kernel

private theorem row_5_21 :
    reconstructed 5 21 =
      (ReleasedGlobal.jointRows 5 21).map (fun p => (p.1.val, p.2)) := by
  decide +kernel

private theorem row_5_22 :
    reconstructed 5 22 =
      (ReleasedGlobal.jointRows 5 22).map (fun p => (p.1.val, p.2)) := by
  decide +kernel

private theorem row_5_25 :
    reconstructed 5 25 =
      (ReleasedGlobal.jointRows 5 25).map (fun p => (p.1.val, p.2)) := by
  decide +kernel

private theorem row_5_26 :
    reconstructed 5 26 =
      (ReleasedGlobal.jointRows 5 26).map (fun p => (p.1.val, p.2)) := by
  decide +kernel

private theorem row_5_27 :
    reconstructed 5 27 =
      (ReleasedGlobal.jointRows 5 27).map (fun p => (p.1.val, p.2)) := by
  decide +kernel

private theorem row_5_28 :
    reconstructed 5 28 =
      (ReleasedGlobal.jointRows 5 28).map (fun p => (p.1.val, p.2)) := by
  decide +kernel

private theorem row_5_31 :
    reconstructed 5 31 =
      (ReleasedGlobal.jointRows 5 31).map (fun p => (p.1.val, p.2)) := by
  decide +kernel

private theorem row_5_32 :
    reconstructed 5 32 =
      (ReleasedGlobal.jointRows 5 32).map (fun p => (p.1.val, p.2)) := by
  decide +kernel

private theorem row_5_33 :
    reconstructed 5 33 =
      (ReleasedGlobal.jointRows 5 33).map (fun p => (p.1.val, p.2)) := by
  decide +kernel

private theorem row_5_36 :
    reconstructed 5 36 =
      (ReleasedGlobal.jointRows 5 36).map (fun p => (p.1.val, p.2)) := by
  decide +kernel

private theorem row_5_37 :
    reconstructed 5 37 =
      (ReleasedGlobal.jointRows 5 37).map (fun p => (p.1.val, p.2)) := by
  decide +kernel

private theorem row_5_40 :
    reconstructed 5 40 =
      (ReleasedGlobal.jointRows 5 40).map (fun p => (p.1.val, p.2)) := by
  decide +kernel

theorem solution (s : Fin 45) :
    (seed 5 s).boundary = [] →
    reconstructed 5 s = (ReleasedGlobal.jointRows 5 s).map (fun p => (p.1.val, p.2)) := by
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
  · exact fun _ => row_5_10
  · exact fun _ => row_5_11
  · exact fun _ => row_5_12
  · exact fun _ => row_5_13
  · exact fun _ => row_5_14
  · exact fun _ => row_5_15
  · decide +kernel
  · decide +kernel
  · exact fun _ => row_5_18
  · exact fun _ => row_5_19
  · exact fun _ => row_5_20
  · exact fun _ => row_5_21
  · exact fun _ => row_5_22
  · decide +kernel
  · decide +kernel
  · exact fun _ => row_5_25
  · exact fun _ => row_5_26
  · exact fun _ => row_5_27
  · exact fun _ => row_5_28
  · decide +kernel
  · decide +kernel
  · exact fun _ => row_5_31
  · exact fun _ => row_5_32
  · exact fun _ => row_5_33
  · decide +kernel
  · decide +kernel
  · exact fun _ => row_5_36
  · exact fun _ => row_5_37
  · decide +kernel
  · decide +kernel
  · exact fun _ => row_5_40
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel

#print axioms solution
