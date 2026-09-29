-- Prove2me | Theorems.Thm_mme_released_joint_interior_owner_child_count
-- name    : mme_released_joint_interior_owner_child_count
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T10:28:07.195505+00:00
-- url     : https://prove2.me/theorems/6678daff-0938-4628-bff6-ec0e03e9ea23
-- title:
--   Owner selection preserves every child-word count
-- statement:
--   Selecting a fixed owner label preserves its exact child-word count under the split-coordinate permutation, including complemented halves. This is an equality usable in either restriction direction. The root exponent bound remains a separate obligation.
-- source:
--   Checked tensor restrictions and released global histogram extraction.

import Definitions.Def_mme_released_joint_interior_frame
import Theorems.Thm_mme_recursive_split_coordinate_complement
import Theorems.Thm_mme_recursive_yz_count_full_cell
open MME MME.CompleteSplit MME.RecursiveYZ MME.ReleasedJointInterior

theorem mme_released_joint_interior_owner_child_count
    (k : ℕ) (j : Fin 270)
    (a : ∀ r : Fin 6, Address 4 270 (parent r) (size r k))
    (f : ∀ r : Fin 6, Position (size r k) → CompleteWord 2)
    (r : Fin 6) (c : ReleasedInterior.Split (component j).2) (w : CompleteWord 2) :
    count (fullCell (ReleasedInterior.parent_total (component j).2)
      (fun r t => (splitEquiv r j).symm (a r j t)))
      (fun p => f p.1 ⟨j,p.2⟩) ⟨r,c⟩ w =
    count (fullCell (parent_total r) (a r)) (f r) ⟨j,splitEquiv r j c⟩ w := by sorry
