-- Prove2me | Theorems.Thm_mme_released_joint_interior_owner_reference_target
-- name    : mme_released_joint_interior_owner_reference_target
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T10:08:36.660538+00:00
-- url     : https://prove2.me/theorems/67634f4c-3aae-4d41-bc84-1f78792988ff
-- title:
--   Joint addresses recover the exact owner split histogram
-- statement:
--   Undoing the joint split-coordinate permutation reconstructs an address in the exact target family for every owner-parent label, including zero-weight labels. The root exponent bound remains a separate obligation.
-- source:
--   Checked tensor restrictions and released global histogram extraction.

import Definitions.Def_mme_released_joint_interior_frame
import Definitions.Def_mme_recursive_x_hash_families
open MME MME.RecursiveYZ MME.ReleasedJointInterior

theorem mme_released_joint_interior_owner_reference_target
    (k : ℕ) (j : Fin 270)
    (a : ∀ r : Fin 6, Address 4 270 (parent r) (size r k))
    (ha : ∀ r, a r ∈ RecursiveXHash.target (n := size r k) (splitCount r k)) :
    (fun r t => (splitEquiv r j).symm (a r j t)) ∈
      RecursiveXHash.target
        (n := fun r => k * weight j * ReleasedInterior.regionalSize
          (component j).1 (component j).2 r)
        (fun r c => k * weight j * ReleasedInterior.splitCount
          (component j).1 (component j).2 r c) := by sorry
