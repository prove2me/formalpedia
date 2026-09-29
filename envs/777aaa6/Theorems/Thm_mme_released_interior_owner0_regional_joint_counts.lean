-- Prove2me | Theorems.Thm_mme_released_interior_owner0_regional_joint_counts
-- name    : mme_released_interior_owner0_regional_joint_counts
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T04:12:44.542785+00:00
-- url     : https://prove2.me/theorems/bda26599-d19a-4087-8c90-e0474c628be1
-- title:
--   Released interior reconstruction for owner 0
-- statement:
--   For owner 0, every released interior recipe reconstructs exactly the released global list of joint counts. The six weighted independent child products are combined, zero entries removed, and atom indices sorted. This is an exact finite arithmetic identity; no exponent bound is claimed.
-- source:
--   Released exact seed and global joint profile data.

import Definitions.Def_mme_released_interior_integer_profiles
open MME MME.ReleasedInterior

theorem mme_released_interior_owner0_regional_joint_counts (s : Fin 45) :
    (seed 0 s).boundary = [] →
    reconstructed 0 s = (ReleasedGlobal.jointRows 0 s).map (fun p => (p.1.val, p.2)) := by sorry
