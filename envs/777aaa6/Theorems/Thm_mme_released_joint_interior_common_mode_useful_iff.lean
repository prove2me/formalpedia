-- Prove2me | Theorems.Thm_mme_released_joint_interior_common_mode_useful_iff
-- name    : mme_released_joint_interior_common_mode_useful_iff
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T15:33:27.873296+00:00
-- url     : https://prove2.me/theorems/378aded4-569a-4cea-8bd6-03d10ce42934
-- title:
--   Common-mode joint and owner histograms are equivalent
-- statement:
--   The six joint exact child histograms hold if and only if every selected owner has its exact released child histogram, after returning each whole tensor to common source mode order. Zero-sized labels are included. The root exponent bound remains a separate obligation.
-- source:
--   Checked tensor restrictions and released global histogram extraction.

import Theorems.Thm_mme_released_joint_interior_owner_useful
open MME MME.CompleteSplit MME.RecursiveYZ MME.ReleasedJointInterior

theorem mme_released_joint_interior_common_mode_useful_iff
    (k : ℕ) (i : Fin 3)
    (a : ∀ r : Fin 6, Address 4 270 (parent r) (size r k))
    (f : ∀ r : Fin 6, Position (size r k) → CompleteWord 2) :
    (∀ r : Fin 6, Useful (fullCell (parent_total r) (a r))
      (integerProfile r k ((roleEquiv r).symm i)) (f r)) ↔
    ∀ j : Fin 270,
      Useful (fullCell (ReleasedInterior.parent_total (component j).2)
        (fun r t => (splitEquiv r j).symm (a r j t)))
        (fun c w => k * weight j * ReleasedInterior.integerProfile
          (component j).1 (component j).2 ((roleEquiv (component j).1).symm i) c w)
        (fun p => f p.1 ⟨j,p.2⟩) := by sorry
