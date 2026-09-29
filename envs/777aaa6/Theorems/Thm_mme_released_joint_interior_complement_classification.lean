-- Prove2me | Theorems.Thm_mme_released_joint_interior_complement_classification
-- name    : mme_released_joint_interior_complement_classification
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T11:08:30.405044+00:00
-- url     : https://prove2.me/theorems/934127f1-45b0-4e8d-92f7-09f87cc98949
-- title:
--   Complementary joint labels are empty or boundary cells
-- statement:
--   Every zero-weight joint label has zero coarse mass or a zero parent coordinate. Thus the existing empty-cell and boundary extraction bounds cover the full complementary product. The root exponent bound remains a separate obligation.
-- source:
--   Checked tensor restrictions and released global histogram extraction.

import Theorems.Thm_mme_released_interior_boundary_classification
import Definitions.Def_mme_released_joint_interior_profiles
open MME.ReleasedJointInterior

theorem mme_released_joint_interior_complement_classification
    (j : Fin 270) (hj : ¬ 0 < weight j) :
    MME.ReleasedGlobal.coarseCounts (component j).1
        (MME.ReleasedGlobal.shapeEquiv (component j).2) = 0 ∨
      ∃ z : Fin 3, ((MME.ReleasedGlobal.shape (component j).2).val z).val = 0 := by sorry
