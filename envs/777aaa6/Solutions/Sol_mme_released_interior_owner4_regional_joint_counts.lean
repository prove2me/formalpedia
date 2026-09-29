-- Prove2me | solution 1 for mme_released_interior_owner4_regional_joint_counts
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T04:14:29.944747+00:00
-- url     : https://prove2.me/submissions/618c80bf-30bf-417c-bf44-4242f2457162

import Definitions.Def_mme_released_interior_integer_profiles
open MME MME.ReleasedInterior

private theorem row_4_10 :
    reconstructed 4 10 =
      (ReleasedGlobal.jointRows 4 10).map (fun p => (p.1.val, p.2)) := by
  decide +kernel

private theorem row_4_11 :
    reconstructed 4 11 =
      (ReleasedGlobal.jointRows 4 11).map (fun p => (p.1.val, p.2)) := by
  decide +kernel

private theorem row_4_12 :
    reconstructed 4 12 =
      (ReleasedGlobal.jointRows 4 12).map (fun p => (p.1.val, p.2)) := by
  decide +kernel

private theorem row_4_13 :
    reconstructed 4 13 =
      (ReleasedGlobal.jointRows 4 13).map (fun p => (p.1.val, p.2)) := by
  decide +kernel

private theorem row_4_14 :
    reconstructed 4 14 =
      (ReleasedGlobal.jointRows 4 14).map (fun p => (p.1.val, p.2)) := by
  decide +kernel

private theorem row_4_15 :
    reconstructed 4 15 =
      (ReleasedGlobal.jointRows 4 15).map (fun p => (p.1.val, p.2)) := by
  decide +kernel

private theorem row_4_18 :
    reconstructed 4 18 =
      (ReleasedGlobal.jointRows 4 18).map (fun p => (p.1.val, p.2)) := by
  decide +kernel

private theorem row_4_19 :
    reconstructed 4 19 =
      (ReleasedGlobal.jointRows 4 19).map (fun p => (p.1.val, p.2)) := by
  decide +kernel

private theorem row_4_20 :
    reconstructed 4 20 =
      (ReleasedGlobal.jointRows 4 20).map (fun p => (p.1.val, p.2)) := by
  decide +kernel

private theorem row_4_21 :
    reconstructed 4 21 =
      (ReleasedGlobal.jointRows 4 21).map (fun p => (p.1.val, p.2)) := by
  decide +kernel

private theorem row_4_22 :
    reconstructed 4 22 =
      (ReleasedGlobal.jointRows 4 22).map (fun p => (p.1.val, p.2)) := by
  decide +kernel

private theorem row_4_25 :
    reconstructed 4 25 =
      (ReleasedGlobal.jointRows 4 25).map (fun p => (p.1.val, p.2)) := by
  decide +kernel

private theorem row_4_26 :
    reconstructed 4 26 =
      (ReleasedGlobal.jointRows 4 26).map (fun p => (p.1.val, p.2)) := by
  decide +kernel

private theorem row_4_27 :
    reconstructed 4 27 =
      (ReleasedGlobal.jointRows 4 27).map (fun p => (p.1.val, p.2)) := by
  decide +kernel

private theorem row_4_28 :
    reconstructed 4 28 =
      (ReleasedGlobal.jointRows 4 28).map (fun p => (p.1.val, p.2)) := by
  decide +kernel

private theorem row_4_31 :
    reconstructed 4 31 =
      (ReleasedGlobal.jointRows 4 31).map (fun p => (p.1.val, p.2)) := by
  decide +kernel

private theorem row_4_32 :
    reconstructed 4 32 =
      (ReleasedGlobal.jointRows 4 32).map (fun p => (p.1.val, p.2)) := by
  decide +kernel

private theorem row_4_33 :
    reconstructed 4 33 =
      (ReleasedGlobal.jointRows 4 33).map (fun p => (p.1.val, p.2)) := by
  decide +kernel

private theorem row_4_36 :
    reconstructed 4 36 =
      (ReleasedGlobal.jointRows 4 36).map (fun p => (p.1.val, p.2)) := by
  decide +kernel

private theorem row_4_37 :
    reconstructed 4 37 =
      (ReleasedGlobal.jointRows 4 37).map (fun p => (p.1.val, p.2)) := by
  decide +kernel

private theorem row_4_40 :
    reconstructed 4 40 =
      (ReleasedGlobal.jointRows 4 40).map (fun p => (p.1.val, p.2)) := by
  decide +kernel

theorem solution (s : Fin 45) :
    (seed 4 s).boundary = [] →
    reconstructed 4 s = (ReleasedGlobal.jointRows 4 s).map (fun p => (p.1.val, p.2)) := by
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
  · exact fun _ => row_4_10
  · exact fun _ => row_4_11
  · exact fun _ => row_4_12
  · exact fun _ => row_4_13
  · exact fun _ => row_4_14
  · exact fun _ => row_4_15
  · decide +kernel
  · decide +kernel
  · exact fun _ => row_4_18
  · exact fun _ => row_4_19
  · exact fun _ => row_4_20
  · exact fun _ => row_4_21
  · exact fun _ => row_4_22
  · decide +kernel
  · decide +kernel
  · exact fun _ => row_4_25
  · exact fun _ => row_4_26
  · exact fun _ => row_4_27
  · exact fun _ => row_4_28
  · decide +kernel
  · decide +kernel
  · exact fun _ => row_4_31
  · exact fun _ => row_4_32
  · exact fun _ => row_4_33
  · decide +kernel
  · decide +kernel
  · exact fun _ => row_4_36
  · exact fun _ => row_4_37
  · decide +kernel
  · decide +kernel
  · exact fun _ => row_4_40
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel

#print axioms solution
