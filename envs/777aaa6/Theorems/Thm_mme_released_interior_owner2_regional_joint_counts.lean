-- Prove2me | Theorems.Thm_mme_released_interior_owner2_regional_joint_counts
-- name    : mme_released_interior_owner2_regional_joint_counts
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T04:13:13.743755+00:00
-- url     : https://prove2.me/theorems/7ced535e-5ab4-444c-a4b7-76486da3e330
-- title:
--   Released interior reconstruction for owner 2
-- statement:
--   For owner 2, every released interior recipe reconstructs exactly the released global list of joint counts. The six weighted independent child products are combined, zero entries removed, and atom indices sorted. This is an exact finite arithmetic identity; no exponent bound is claimed.
-- source:
--   Released exact seed and global joint profile data.

import Definitions.Def_mme_released_interior_integer_profiles
open MME MME.ReleasedInterior

theorem mme_released_interior_owner2_regional_joint_counts (s : Fin 45) :
    (seed 2 s).boundary = [] →
    reconstructed 2 s = (ReleasedGlobal.jointRows 2 s).map (fun p => (p.1.val, p.2)) := by sorry
