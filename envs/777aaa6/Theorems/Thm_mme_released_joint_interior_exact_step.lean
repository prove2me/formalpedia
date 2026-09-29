-- Prove2me | Theorems.Thm_mme_released_joint_interior_exact_step
-- name    : mme_released_joint_interior_exact_step
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T10:00:11.859038+00:00
-- url     : https://prove2.me/theorems/20ae8591-f5dd-48dc-bf27-8a7a63ed4ab8
-- title:
--   A joint extraction step for the released inner profiles
-- statement:
--   Under the explicit concentration inequality, one graded extraction step acts on all 270 owner and parent labels, with an exact copy lower bound, repair exponent, and output predicate. Connecting this common parent-typical source to the outer extraction remains a separate obligation. The root exponent bound remains a separate obligation.
-- source:
--   Checked tensor restrictions and released global histogram extraction.

import Theorems.Thm_mme_released_joint_interior_integer_constraints
import Theorems.Thm_mme_released_joint_interior_positive_blocks
import Theorems.Thm_mme_recursive_region_graded_source_exact_step_allow_empty
open scoped BigOperators
open MME MME.ReleasedJointInterior MME.RecursiveYZ MME.RegionRealization
open MME.ProfiledCW MME.CompleteSplit MME.MoreAsymmetryExactSeed
open MME.RecursiveYZ.Certificate MME.RecursiveYZ.CWCells

theorem mme_released_joint_interior_exact_step
    (r : Fin 6) (k : ℕ) (hk : 0 < k) (d : ℕ) (hd : 1 < d)
    (eps : ℝ) (heps : 0 < eps)
    (hscale : (8 * d : ℝ) * (25 * 270 * (Fintype.card (CompleteWord 2) : ℝ) ^ 2) ≤
      (k * denominator ^ 2 : ℕ) * eps ^ 2) :
    let keep := fun (i : Fin 2)
      (_ : RecursiveXHash.Address 4 270 (parent r) (size r k)) =>
        parentTypical (parent_total r) (size r k) (splitCount r k)
          (integerProfile r k (yzMode i)) eps
    let Q := commonScale 4
      (loadNum (parent_total r) (splitCount r k) d
        (fun i => integerProfile r k (yzMode i)) keep) (loadDen (splitCount r k))
    ∃ reference : RecursiveXHash.Address 4 270 (parent r) (size r k),
      reference ∈ RecursiveXHash.target (n := size r k) (splitCount r k) ∧
      ∃ E : ExactStep 2 (blocks r k * 4) (source r k eps),
        ((RecursiveXHash.target (n := size r k) (splitCount r k)).card : ℝ) *
          Real.exp (-4 * Real.sqrt (Real.log Q)) / (32 * Q) ≤ E.count ∧
        E.stage.repairExponent = Nat.log d
          (∏ i : Fin 3, Nat.card (Block 2 (fullCell (parent_total r) reference)
            (fun c i => (c.2.val i).val) (integerProfile r k) i)) + 1 ∧
        E.output = fun i x =>
          Graded (parent_total r) i reference
            (ProfiledCW.split (positions r k) (positions_length r k) x) ∧
          Useful (fullCell (parent_total r) reference) (integerProfile r k i)
            (ProfiledCW.split (positions r k) (positions_length r k) x) := by sorry
