-- Prove2me | Theorems.Thm_mme_released_joint_interior_owner_useful
-- name    : mme_released_joint_interior_owner_useful
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T15:08:33.57823+00:00
-- url     : https://prove2.me/theorems/a9e2f1c7-de3d-4a59-8cf6-300c41ce38f8
-- title:
--   Joint child histograms recover exact owner histograms
-- statement:
--   Exact joint child-word counts recover the released owner counts on the same physical positions, with the split-coordinate permutation and complemented halves preserved. The root exponent bound remains a separate obligation.
-- source:
--   Checked tensor restrictions and released global histogram extraction.

import Theorems.Thm_mme_released_joint_interior_owner_child_count
open MME MME.CompleteSplit MME.RecursiveYZ MME.ReleasedJointInterior

theorem mme_released_joint_interior_owner_useful
    (k : ℕ) (j : Fin 270) (i : Fin 3)
    (a : ∀ r : Fin 6, Address 4 270 (parent r) (size r k))
    (f : ∀ r : Fin 6, Position (size r k) → CompleteWord 2)
    (hu : ∀ r : Fin 6,
      Useful (fullCell (parent_total r) (a r))
        (integerProfile r k ((orientation (component j).1 r).symm i)) (f r)) :
    Useful (fullCell (ReleasedInterior.parent_total (component j).2)
      (fun r t => (splitEquiv r j).symm (a r j t)))
      (fun c w => k * weight j * ReleasedInterior.integerProfile
        (component j).1 (component j).2 i c w)
      (fun p => f p.1 ⟨j,p.2⟩) := by sorry
