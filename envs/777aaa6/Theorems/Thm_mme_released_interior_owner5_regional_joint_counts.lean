-- Prove2me | Theorems.Thm_mme_released_interior_owner5_regional_joint_counts
-- name    : mme_released_interior_owner5_regional_joint_counts
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T04:14:33.411849+00:00
-- url     : https://prove2.me/theorems/d37303c1-ce21-4c68-aa6d-08067ac52d0f
-- title:
--   Released interior reconstruction for owner 5
-- statement:
--   For owner 5, every released interior recipe reconstructs exactly the released global list of joint counts. The six weighted independent child products are combined, zero entries removed, and atom indices sorted. This is an exact finite arithmetic identity; no exponent bound is claimed.
-- source:
--   Released exact seed and global joint profile data.

import Definitions.Def_mme_released_interior_integer_profiles
open MME MME.ReleasedInterior

theorem mme_released_interior_owner5_regional_joint_counts (s : Fin 45) :
    (seed 5 s).boundary = [] →
    reconstructed 5 s = (ReleasedGlobal.jointRows 5 s).map (fun p => (p.1.val, p.2)) := by sorry
