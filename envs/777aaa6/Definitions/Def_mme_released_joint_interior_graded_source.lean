-- Prove2me | Definitions.Def_mme_released_joint_interior_graded_source
-- name    : mme_released_joint_interior_graded_source
-- status  : Definition
-- author  : @Robertboy18
-- created : 2026-09-23T09:55:55.310146+00:00
-- url     : https://prove2.me/theorems/24fe658a-4862-4b25-9942-3bd764a54d32
-- title:
--   The joint source over all prescribed addresses
-- statement:
--   The parent-typical source retains every graded address with the prescribed joint split histogram. Addresses may depend on the mode and word; hashing selects from the entire target family rather than a fixed reference address.

import Definitions.Def_mme_released_joint_interior_frame
import Definitions.Def_mme_recursive_x_hash_families

namespace MME.ReleasedJointInterior

/-- The source window retains every target address with the prescribed joint
split histogram. Its address may depend on the mode and word; no reference
address is fixed before the hashing extraction. -/
noncomputable def gradedSource (r : Fin 6) (k : ℕ) (epsilon : ℝ) :
    ProfiledCW.Predicate (blocks r k * 4) :=
  fun i x => source r k epsilon i x ∧
    ∃ a : RecursiveXHash.Address 4 270 (parent r) (size r k),
      a ∈ RecursiveXHash.target (n := size r k) (splitCount r k) ∧
      RecursiveYZ.Graded (parent_total r) i a
        (ProfiledCW.split (positions r k) (positions_length r k) x)

end MME.ReleasedJointInterior


