-- Prove2me | Theorems.Thm_mme_released_interior_owner4_regional_joint_counts
-- name    : mme_released_interior_owner4_regional_joint_counts
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T04:14:14.914316+00:00
-- url     : https://prove2.me/theorems/548c939d-0576-4389-a5d9-8a1a37f326f3
-- title:
--   Released interior reconstruction for owner 4
-- statement:
--   For owner 4, every released interior recipe reconstructs exactly the released global list of joint counts. The six weighted independent child products are combined, zero entries removed, and atom indices sorted. This is an exact finite arithmetic identity; no exponent bound is claimed.
-- source:
--   Released exact seed and global joint profile data.

import Definitions.Def_mme_released_interior_integer_profiles
open MME MME.ReleasedInterior

theorem mme_released_interior_owner4_regional_joint_counts (s : Fin 45) :
    (seed 4 s).boundary = [] →
    reconstructed 4 s = (ReleasedGlobal.jointRows 4 s).map (fun p => (p.1.val, p.2)) := by sorry
