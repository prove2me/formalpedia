-- Prove2me | Theorems.Thm_mme_released_interior_regional_joint_counts_exact
-- name    : mme_released_interior_regional_joint_counts_exact
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T04:23:42.296455+00:00
-- url     : https://prove2.me/theorems/a9810b35-b5a9-49af-86fa-5852d6123592
-- title:
--   All released interior joint counts reconstruct exactly
-- statement:
--   For all six owners and every released interior recipe, combining the weighted independent square-child products reconstructs the exact released global joint-count list. This assembles six owner-specific certificates and retains zero-sized regions. It is the reconstruction identity, not the full matrix exponent bound.
-- source:
--   Six owner-specific exact reconstruction certificates.

import Theorems.Thm_mme_released_interior_owner0_regional_joint_counts
import Theorems.Thm_mme_released_interior_owner1_regional_joint_counts
import Theorems.Thm_mme_released_interior_owner2_regional_joint_counts
import Theorems.Thm_mme_released_interior_owner3_regional_joint_counts
import Theorems.Thm_mme_released_interior_owner4_regional_joint_counts
import Theorems.Thm_mme_released_interior_owner5_regional_joint_counts

open MME MME.ReleasedInterior

theorem mme_released_interior_regional_joint_counts_exact (owner : Fin 6) (s : Fin 45) :
    (seed owner s).boundary = [] →
    reconstructed owner s = (ReleasedGlobal.jointRows owner s).map (fun p => (p.1.val, p.2)) := by sorry
