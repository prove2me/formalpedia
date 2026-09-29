-- Prove2me | Theorems.Thm_mme_released_interior_owner3_regional_joint_counts
-- name    : mme_released_interior_owner3_regional_joint_counts
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T04:14:01.415779+00:00
-- url     : https://prove2.me/theorems/d368fcfe-c4ec-4e2b-9f3f-cfaf6f0732ef
-- title:
--   Released interior reconstruction for owner 3
-- statement:
--   For owner 3, every released interior recipe reconstructs exactly the released global list of joint counts. The six weighted independent child products are combined, zero entries removed, and atom indices sorted. This is an exact finite arithmetic identity; no exponent bound is claimed.
-- source:
--   Released exact seed and global joint profile data.

import Definitions.Def_mme_released_interior_integer_profiles
open MME MME.ReleasedInterior

theorem mme_released_interior_owner3_regional_joint_counts (s : Fin 45) :
    (seed 3 s).boundary = [] →
    reconstructed 3 s = (ReleasedGlobal.jointRows 3 s).map (fun p => (p.1.val, p.2)) := by sorry
