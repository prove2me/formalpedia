-- Prove2me | solution 1 for mme_released_interior_owner1_cell28_region1_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T14:55:36.016652+00:00
-- url     : https://prove2.me/submissions/d3bc9031-3860-406f-bf87-e0c0df1bfb29

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 28) : ℚ :=
  (splitWeight 1 28 1 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(1395012006730000000000000000000000 / 88425518652070250154022809710533413), (7027811016940000000000000000000000 / 88425518652070250154022809710533413), (780869079895000000000000000000000 / 9825057628007805572669201078948157), (1395018173770000000000000000000000 / 88425518652070250154022809710533413), (1 / 1)], ![(26535103139 / 500000000000), (2005008582543 / 1000000000000), (13632631958477 / 1000000000000), (2005014710157 / 1000000000000), (5307021723 / 100000000000)], ![(49007830923 / 125000000000), (4900790581 / 12500000000), (1 / 1), (1 / 1), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![6, 4, 4, 6, 0], ![5, -1, -3, -1, 5], ![2, 2, 0, 0, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-414925757831 / 100000000000), (-1266142660289 / 500000000000), (-506456759551 / 200000000000), (-207462657877 / 50000000000), (0 / 1)], ![(-1468069797623 / 500000000000), (695648341319 / 1000000000000), (653116581867 / 250000000000), (173912849367 / 250000000000), (-1468069694439 / 500000000000)], ![(-468166818603 / 500000000000), (-187266421829 / 200000000000), (0 / 1), (0 / 1), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-4149257578309 / 1000000000000), (-2532285320577 / 1000000000000), (-1266141898877 / 500000000000), (-4149253157539 / 1000000000000), (0 / 1)], ![(-587227919049 / 200000000000), (17391208533 / 25000000000), (2612466327469 / 1000000000000), (695651397469 / 1000000000000), (-2936139388877 / 1000000000000)], ![(-187266727441 / 200000000000), (-117041513643 / 125000000000), (0 / 1), (0 / 1), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 28) : ℤ :=
  ([12, 7, 5, 2, 2, 5, 7, 12] : List ℤ).getD
    ((seed 1 28).splits.idxOf (sourceShape 1 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 28) : ℚ :=
  ([(-1604346120611 / 200000000000), (-877987658001 / 200000000000), (-277296756031 / 100000000000), (-171230220451 / 200000000000), (-856151107493 / 1000000000000), (-346620945697 / 125000000000), (-4389938453453 / 1000000000000), (-8021724860523 / 1000000000000)] : List ℚ).getD
    ((seed 1 28).splits.idxOf (sourceShape 1 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 28) : ℚ :=
  ([(-4010865301527 / 500000000000), (-1097484572501 / 250000000000), (-2772967560309 / 1000000000000), (-428075551127 / 500000000000), (-214037776873 / 250000000000), (-110918702623 / 40000000000), (-1097484613363 / 250000000000), (-4010862430261 / 500000000000)] : List ℚ).getD
    ((seed 1 28).splits.idxOf (sourceShape 1 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 28) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 28 =>
        (splitWeight 1 28 1 c : ℝ) / 1000000000000) ≤
          (1 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 28, ∏ i, weights i (c.val i) ≤ 1 := by
    decide +kernel
  have h := mme_rational_product_dual_penalty_certificate alphaQ
    (fun c => (alpha_pos c).le) hprob weights weights_pos hmass weightLower alphaUpper
    (fun i j => (weight_logs i j).1) (fun c _ => (alpha_logs c).2)
    (1 / 1000000000)
  have hbound : Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c => (alphaQ c : ℝ)) ≤ ((1 / 1000000000 : ℚ) : ℝ) := by
    apply h
    decide +kernel
  simpa only [alphaQ, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat,
    Rat.cast_one, Rat.cast_zero] using hbound


#print axioms solution
