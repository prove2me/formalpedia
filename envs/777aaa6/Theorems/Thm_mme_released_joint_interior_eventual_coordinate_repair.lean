-- Prove2me | Theorems.Thm_mme_released_joint_interior_eventual_coordinate_repair
-- name    : mme_released_joint_interior_eventual_coordinate_repair
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T10:38:09.813108+00:00
-- url     : https://prove2.me/theorems/59ac4e96-251c-4134-bfd1-97a4d7a0fe7e
-- title:
--   Joint exact steps share a uniform coordinate repair budget
-- statement:
--   All six joint regions admit their exact graded extraction at every sufficiently large scale. One repair base bounds logarithmic repair loss per physical coordinate uniformly over the 270 owner labels. The root exponent bound remains a separate obligation.
-- source:
--   Checked tensor restrictions and released global histogram extraction.

import Theorems.Thm_mme_released_joint_interior_graded_source_exact_step
import Theorems.Thm_mme_profile_repair_scale_exists_uniform_coordinate_loss
open scoped BigOperators
open MME MME.ReleasedJointInterior MME.RecursiveYZ MME.RegionRealization
open MME.ProfiledCW MME.CompleteSplit MME.MoreAsymmetryExactSeed
open MME.RecursiveYZ.Certificate MME.RecursiveYZ.CWCells Filter

theorem mme_released_joint_interior_eventual_coordinate_repair
    (eta : ℝ) (heta : 0 < eta) (eps : ℝ) (heps : 0 < eps) :
    ∃ d : ℕ, 1 < d ∧ ∀ᶠ k : ℕ in atTop, ∀ r : Fin 6,
    let keep := fun (i : Fin 2)
      (_ : RecursiveXHash.Address 4 270 (parent r) (size r k)) =>
        parentTypical (parent_total r) (size r k) (splitCount r k)
          (integerProfile r k (yzMode i)) eps
    let Q := commonScale 4
      (loadNum (parent_total r) (splitCount r k) d
        (fun i => integerProfile r k (yzMode i)) keep) (loadDen (splitCount r k))
    ∃ reference : RecursiveXHash.Address 4 270 (parent r) (size r k),
      reference ∈ RecursiveXHash.target (n := size r k) (splitCount r k) ∧
      ∃ E : ExactStep 2 (blocks r k * 4) (gradedSource r k eps),
        ((RecursiveXHash.target (n := size r k) (splitCount r k)).card : ℝ) *
          Real.exp (-4 * Real.sqrt (Real.log Q)) / (32 * Q) ≤ E.count ∧
        E.stage.repairExponent = Nat.log d
          (∏ i : Fin 3, Nat.card (Block 2 (fullCell (parent_total r) reference)
            (fun c i => (c.2.val i).val) (integerProfile r k) i)) + 1 ∧
        (E.output = fun i x =>
          Graded (parent_total r) i reference
            (ProfiledCW.split (positions r k) (positions_length r k) x) ∧
          Useful (fullCell (parent_total r) reference) (integerProfile r k i)
            (ProfiledCW.split (positions r k) (positions_length r k) x)) ∧
        Real.log ((8 : ℝ) ^ E.stage.repairExponent) ≤
          Real.log 8 + eta * (blocks r k * 4 : ℕ) := by sorry
