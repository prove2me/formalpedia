-- Prove2me | Theorems.Thm_mme_released_interior_owner1_regional_joint_counts
-- name    : mme_released_interior_owner1_regional_joint_counts
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T04:13:55.640895+00:00
-- url     : https://prove2.me/theorems/ab09a0c9-1f78-4b00-a596-7c57460c1e7e
-- title:
--   Released interior reconstruction for owner 1
-- statement:
--   For owner 1, every released interior recipe reconstructs exactly the released global list of joint counts. The six weighted independent child products are combined, zero entries removed, and atom indices sorted. This is an exact finite arithmetic identity; no exponent bound is claimed.
-- source:
--   Released exact seed and global joint profile data.

import Definitions.Def_mme_released_interior_integer_profiles
open MME MME.ReleasedInterior

theorem mme_released_interior_owner1_regional_joint_counts (s : Fin 45) :
    (seed 1 s).boundary = [] →
    reconstructed 1 s = (ReleasedGlobal.jointRows 1 s).map (fun p => (p.1.val, p.2)) := by sorry
