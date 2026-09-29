-- Prove2me | Theorems.Thm_mme_released_joint_interior_eventual_positive_copy_rate
-- name    : mme_released_joint_interior_eventual_positive_copy_rate
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T15:09:38.56914+00:00
-- url     : https://prove2.me/theorems/007b8177-f7e3-435e-8693-44f63702cc01
-- title:
--   Positive pooled surplus gives positive actual copy counts
-- statement:
--   Every joint region with positive pooled entropy surplus eventually has positive repaired copies. Their logarithms retain the regional rate with explicit window, repair, and asymptotic losses. The root exponent bound remains a separate obligation.
-- source:
--   Checked tensor restrictions and released global histogram extraction.

import Theorems.Thm_mme_released_joint_interior_eventual_entropy_copy_rate
open scoped BigOperators
open MME MME.ReleasedJointInterior MME.RecursiveYZ MME.RegionRealization
open MME.ProfiledCW MME.CompleteSplit MME.MoreAsymmetryExactSeed
open MME.RecursiveYZ.Certificate MME.RecursiveYZ.CWCells MME.RegionRate Filter

theorem mme_released_joint_interior_eventual_positive_copy_rate
    (eta : ℝ) (heta : 0 < eta) (loss : ℝ) (hloss : 0 < loss)
    (eps : ℝ) (heps : 0 < eps) :
    ∃ d : ℕ, 1 < d ∧ ∀ᶠ k : ℕ in atTop, ∀ r : Fin 6,
      0 < (regionalRate (parent_total r) (size r 1) (splitCount r 1)
          (integerProfile r 1) - (blocks r 1 : ℝ) *
          entropyModulus (Fin 2 → CompleteWord 2) eps -
          4 * eta * (blocks r 1 : ℝ) - loss) →
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
          Real.log 8 + eta * (blocks r k * 4 : ℕ) ∧
        0 < E.copies ∧
        (regionalRate (parent_total r) (size r 1) (splitCount r 1)
          (integerProfile r 1) - (blocks r 1 : ℝ) *
          entropyModulus (Fin 2 → CompleteWord 2) eps -
          4 * eta * (blocks r 1 : ℝ) - loss) * (k : ℝ) < Real.log E.copies := by sorry
