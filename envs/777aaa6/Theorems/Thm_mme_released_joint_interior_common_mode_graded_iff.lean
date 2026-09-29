-- Prove2me | Theorems.Thm_mme_released_joint_interior_common_mode_graded_iff
-- name    : mme_released_joint_interior_common_mode_graded_iff
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T10:13:06.365072+00:00
-- url     : https://prove2.me/theorems/7eb9c354-3275-419c-9fc8-c007dccb54d9
-- title:
--   Common-mode joint and owner child grades are equivalent
-- statement:
--   The joint child grades hold if and only if all selected-owner child grades hold in common source mode order. Both the left and complemented right halves are preserved. The root exponent bound remains a separate obligation.
-- source:
--   Checked tensor restrictions and released global histogram extraction.

import Theorems.Thm_mme_released_joint_interior_owner_graded
open scoped BigOperators
open MME MME.CompleteSplit MME.RecursiveYZ MME.ReleasedJointInterior

theorem mme_released_joint_interior_common_mode_graded_iff
    (k : ℕ) (i : Fin 3)
    (a : ∀ r : Fin 6, Address 4 270 (parent r) (size r k))
    (f : ∀ r : Fin 6, Position (size r k) → CompleteWord 2) :
    (∀ r : Fin 6, Graded (parent_total r) ((roleEquiv r).symm i) (a r) (f r)) ↔
    ∀ j : Fin 270,
      Graded (ReleasedInterior.parent_total (component j).2)
        ((roleEquiv (component j).1).symm i)
        (fun r t => (splitEquiv r j).symm (a r j t))
        (fun p => f p.1 ⟨j,p.2⟩) := by sorry
