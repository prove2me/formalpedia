-- Prove2me | Theorems.Thm_mme_released_global_boundary_rate_sum_bound
-- name    : mme_released_global_boundary_rate_sum_bound
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-24T05:56:25.298985+00:00
-- url     : https://prove2.me/theorems/f6bc4b50-3f34-41b2-b6af-beafd47be7f8
-- title:
--   Actual outer boundary witnesses satisfy a complete volume sum bound
-- statement:
--   The zero-rate and boundary-profile witnesses supplied by the actual extraction imply an explicit lower bound for the sum over all 270 labels. Uniform free-mode certificates apply to any permitted boundary choice, and a loss of 270 times the boundary loss remains explicit. The root exponent bound remains a separate obligation.
-- source:
--   Checked tensor restrictions and released global histogram extraction.

import Theorems.Thm_mme_released_global_owner0_uniform_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner1_uniform_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner2_uniform_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner3_uniform_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner4_uniform_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner5_uniform_boundary_volume_bound
import Theorems.Thm_mme_boundary_profile_volume_mass_entropy
import Definitions.Def_mme_released_joint_interior_profiles
open scoped BigOperators
open MME MME.RegionRate MME.ReleasedGlobal MME.MoreAsymmetryExactSeed
open MME.ReleasedJointInterior MME.RecursiveYZ.Boundary

theorem mme_released_global_boundary_rate_sum_bound
    (boundaryRate : Fin 270 → ℝ) (boundaryLoss : ℝ) (hloss : 0 ≤ boundaryLoss)
    (hzero : ∀ j, (0 < weight j ∨ coarseCounts (component j).1
      (shapeEquiv (component j).2) = 0) → boundaryRate j = 0)
    (hcert : ∀ j, ¬ 0 < weight j → 0 < coarseCounts (component j).1
      (shapeEquiv (component j).2) →
      ∃ (z : Fin 3) (B : Profile 3 (coarseCounts (component j).1 (shapeEquiv (component j).2))),
        ((shapeEquiv (component j).2).val z).val = 0 ∧
        (∀ i w, wordCounts (component j).1 i (shapeEquiv (component j).2) w = B.mu z i w) ∧
        boundaryRate j = (coarseCounts (component j).1 (shapeEquiv (component j).2) : ℝ) * Real.log 2 *
          mme_modern_entropyBits (fun w ↦ (B.count w : ℝ) /
            (coarseCounts (component j).1 (shapeEquiv (component j).2) : ℝ)) +
          ((∑ w, B.count w * ones w : ℕ) : ℝ) * Real.log 5 - boundaryLoss) :
    (denominator : ℝ) ^ 5 * (337884154359 / 125000000000 : ℝ) -
      270 * boundaryLoss ≤ ∑ j, boundaryRate j := by sorry
