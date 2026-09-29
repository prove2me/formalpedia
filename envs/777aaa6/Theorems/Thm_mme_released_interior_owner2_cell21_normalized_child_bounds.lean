-- Prove2me | Theorems.Thm_mme_released_interior_owner2_cell21_normalized_child_bounds
-- name    : mme_released_interior_owner2_cell21_normalized_child_bounds
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-24T16:19:27.854658+00:00
-- url     : https://prove2.me/theorems/c06c89df-0a7b-45f7-9d08-2f6b1e646c88
-- title:
--   Owner 2 parent 21 has a complete normalized child table
-- statement:
--   An explicit function on all actual child cells has the stated exact rational sum. Every boundary free mode and every interior grade-two mode satisfies its actual normalized entropy and dimension rate bound. Zero-mass regions are included. The root exponent bound remains a separate obligation.
-- source:
--   Checked tensor restrictions and released global histogram extraction.

import Theorems.Thm_mme_released_interior_owner2_cell21_region0_boundary_volume_bound
import Theorems.Thm_mme_released_interior_owner2_cell21_region1_boundary_volume_bound
import Theorems.Thm_mme_released_interior_owner2_cell21_region2_boundary_volume_bound
import Theorems.Thm_mme_released_interior_owner2_cell21_region3_boundary_volume_bound
import Theorems.Thm_mme_released_interior_owner2_cell21_region4_boundary_volume_bound
import Theorems.Thm_mme_released_interior_owner2_cell21_region5_boundary_volume_bound
import Theorems.Thm_mme_released_interior_owner2_cell21_region0_112_weight_rate_bound
import Theorems.Thm_mme_released_interior_owner2_cell21_region1_112_weight_rate_bound
import Theorems.Thm_mme_released_interior_owner2_cell21_region2_112_weight_rate_bound
import Theorems.Thm_mme_released_interior_owner2_cell21_region3_112_weight_rate_bound
import Theorems.Thm_mme_released_interior_owner2_cell21_region4_112_weight_rate_bound
import Theorems.Thm_mme_released_interior_owner2_cell21_region5_112_weight_rate_bound
open scoped BigOperators
open MME MME.RegionRate MME.MoreAsymmetryExactSeed MME.RecursiveYZ
open MME.RegionRealization MME.CompleteSplit MME.RecursiveYZ.Boundary

theorem mme_released_interior_owner2_cell21_normalized_child_bounds :
    ∃ q : Cell 4 6 (ReleasedInterior.parent 21) → ℝ,
      (∑ c, q c) = (33660132323889881532416920466502689059 / 1000000000000000000000000000000000000 : ℝ) ∧
      (∀ c z, (c.2.val z).val = 0 →
        (denominator : ℝ) ^ 4 * q c ≤ 6 * (3952233 / 5000000 : ℝ) *
          (massEntropy (fun w ↦ (ReleasedInterior.integerProfile 2 21 (z + 1) c w : ℝ)) +
            (∑ w, (ReleasedInterior.integerProfile 2 21 (z + 1) c w : ℝ) * (ones w : ℝ)) * Real.log 5)) ∧
      (∀ c z, (∀ i : Fin 3, (c.2.val i).val = if i = z then 2 else 1) →
        let p : ℝ := ((((ReleasedInterior.seed 2 21).children.find?
          (fun a => a.1 == c.1.val && a.2.1 == ReleasedInterior.sourceShape 2 c.2)).getD (0, [], 0)).2.2 : ℝ) / denominator
        q c ≤ (((ReleasedInterior.seed 2 21).region.getD c.1.val 0 : ℝ) / denominator *
          ((ReleasedInterior.splitWeight 2 21 c.1 c.2 + ReleasedInterior.splitWeight 2 21 c.1
            (complement (ReleasedInterior.parent_total 21 c.1) c.2) : ℕ) : ℝ) / denominator / 2) *
          (4 * (entropy ![p, p, 1 - 2 * p] + 2 * Real.log 2) +
            24 * (1 - p) * (3952233 / 5000000 : ℝ) * Real.log 5)) := by sorry
