-- Prove2me | Theorems.Thm_mme_released_joint_interior_eventual_product_copy_rate
-- name    : mme_released_joint_interior_eventual_product_copy_rate
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T15:35:49.601141+00:00
-- url     : https://prove2.me/theorems/ba560e86-17d8-4627-a08a-a02be0b896ee
-- title:
--   All six joint copy counts retain the summed pooled rate
-- statement:
--   At a common sufficiently large scale, all six exact joint outputs have positive multiplicity. The product of their actual repaired copy counts is bounded below by the exponential of the summed pooled regional rates, with all losses explicit. The root exponent bound remains a separate obligation.
-- source:
--   Checked tensor restrictions and released global histogram extraction.

import Theorems.Thm_mme_released_joint_interior_eventual_positive_copy_rate
open scoped BigOperators
open MME MME.ReleasedJointInterior MME.RecursiveYZ MME.RegionRealization
open MME.ProfiledCW MME.CompleteSplit MME.MoreAsymmetryExactSeed
open MME.RecursiveYZ.Certificate MME.RecursiveYZ.CWCells MME.RegionRate Filter

theorem mme_released_joint_interior_eventual_product_copy_rate
    (eta : ℝ) (heta : 0 < eta) (loss : ℝ) (hloss : 0 < loss)
    (eps : ℝ) (heps : 0 < eps) :
    let rate : Fin 6 → ℝ := fun r =>
      regionalRate (parent_total r) (size r 1) (splitCount r 1) (integerProfile r 1) -
        (blocks r 1 : ℝ) * entropyModulus (Fin 2 → CompleteWord 2) eps -
        4 * eta * (blocks r 1 : ℝ) - loss
    (∀ r, 0 < rate r) → ∀ᶠ k : ℕ in atTop,
      ∃ (a : ∀ r : Fin 6, Address 4 270 (parent r) (size r k))
        (E : ∀ r : Fin 6, ExactStep 2 (blocks r k * 4) (gradedSource r k eps)),
        (∀ r, a r ∈ RecursiveXHash.target (n := size r k) (splitCount r k)) ∧
        (∀ r, (E r).output = fun i x =>
          Graded (parent_total r) i (a r)
            (ProfiledCW.split (positions r k) (positions_length r k) x) ∧
          Useful (fullCell (parent_total r) (a r)) (integerProfile r k i)
            (ProfiledCW.split (positions r k) (positions_length r k) x)) ∧
        (∀ r, 0 < (E r).copies) ∧
        0 < ∏ r, (E r).copies ∧
        Real.exp ((∑ r, rate r) * (k : ℝ)) ≤ (∏ r, (E r).copies : ℕ) := by sorry
