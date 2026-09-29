-- Prove2me | Theorems.Thm_mme_released_joint_interior_owner_graded
-- name    : mme_released_joint_interior_owner_graded
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T09:44:43.82275+00:00
-- url     : https://prove2.me/theorems/efd2bf29-3d38-49d3-9ddd-d86eec433859
-- title:
--   Joint child grades recover owner child grades
-- statement:
--   Reading joint child grades in a fixed owner mode order gives exactly the grades of the reconstructed owner address on the same physical words. The root exponent bound remains a separate obligation.
-- source:
--   Checked tensor restrictions and released global histogram extraction.

import Definitions.Def_mme_released_joint_interior_frame
open scoped BigOperators
open MME MME.RecursiveYZ MME.RegionRealization MME.CompleteSplit
open MME.ReleasedJointInterior

theorem mme_released_joint_interior_owner_graded
    (k : ℕ) (j : Fin 270) (i : Fin 3)
    (a : ∀ r : Fin 6, Address 4 270 (parent r) (size r k))
    (f : ∀ r : Fin 6, Position (size r k) → CompleteWord 2)
    (hg : ∀ r : Fin 6,
      Graded (parent_total r) ((orientation (component j).1 r).symm i) (a r) (f r)) :
    Graded (ReleasedInterior.parent_total (component j).2) i
      (fun r t => (splitEquiv r j).symm (a r j t))
      (fun p => f p.1 ⟨j,p.2⟩) := by sorry
