-- Prove2me | solution 1 for mme_released_interior_regional_joint_counts_exact
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T04:25:55.689881+00:00
-- url     : https://prove2.me/submissions/a89810a6-787d-4f8a-a358-0de6e578789e

import Theorems.Thm_mme_released_interior_owner0_regional_joint_counts
import Theorems.Thm_mme_released_interior_owner1_regional_joint_counts
import Theorems.Thm_mme_released_interior_owner2_regional_joint_counts
import Theorems.Thm_mme_released_interior_owner3_regional_joint_counts
import Theorems.Thm_mme_released_interior_owner4_regional_joint_counts
import Theorems.Thm_mme_released_interior_owner5_regional_joint_counts

open MME MME.ReleasedInterior

theorem solution (owner : Fin 6) (s : Fin 45) :
    (seed owner s).boundary = [] →
    reconstructed owner s = (ReleasedGlobal.jointRows owner s).map (fun p => (p.1.val, p.2)) := by
  fin_cases owner
  · exact mme_released_interior_owner0_regional_joint_counts s
  · exact mme_released_interior_owner1_regional_joint_counts s
  · exact mme_released_interior_owner2_regional_joint_counts s
  · exact mme_released_interior_owner3_regional_joint_counts s
  · exact mme_released_interior_owner4_regional_joint_counts s
  · exact mme_released_interior_owner5_regional_joint_counts s

#print axioms solution
