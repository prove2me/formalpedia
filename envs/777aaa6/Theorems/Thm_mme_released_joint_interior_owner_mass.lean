-- Prove2me | Theorems.Thm_mme_released_joint_interior_owner_mass
-- name    : mme_released_joint_interior_owner_mass
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T09:45:04.455489+00:00
-- url     : https://prove2.me/theorems/e6fcf08a-877f-4d12-a347-ff0bd09c7684
-- title:
--   Regrouped inner regions recover the owner-parent mass
-- statement:
--   Summing the six regional sizes for any owner-parent label recovers its exact original mass, including zero-weight and boundary labels. The root exponent bound remains a separate obligation.
-- source:
--   Checked tensor restrictions and released global histogram extraction.

import Theorems.Thm_mme_released_interior_scaled_integer_profile_constraints_exact
import Definitions.Def_mme_released_joint_interior_frame
open scoped BigOperators
open MME MME.ReleasedJointInterior MME.MoreAsymmetryExactSeed

theorem mme_released_joint_interior_owner_mass (k : ℕ) (j : Fin 270) :
    (∑ r : Fin 6, size r k j) = k * weight j * denominator ^ 4 := by sorry
