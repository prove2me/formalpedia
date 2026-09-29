-- Prove2me | solution 1 for mme_released_interior_owner5_cell37_region0_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-24T09:24:18.182973+00:00
-- url     : https://prove2.me/submissions/9d793b82-0694-4f46-b0c4-410dc0519ad7

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 37) : ℚ :=
  (splitWeight 5 37 0 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(1 / 1), (157931161369 / 1000000000000), (759832824703 / 200000000000), (474895356391 / 125000000000), (15793058177 / 100000000000)], ![(117416757317 / 200000000000), (1044560459497 / 1000000000000), (117416667257 / 200000000000), (1 / 1), (1 / 1)], ![(200007292953000000000000000000000000 / 2516731679384180253039922781118236473), (200007214724000000000000000000000000 / 2516731679384180253039922781118236473), (1 / 1), (1 / 1), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![0, 3, -1, -1, 3], ![1, 0, 1, 0, 0], ![4, 4, 0, 0, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(0 / 1), (-1845596028433 / 1000000000000), (1334781075039 / 1000000000000), (1334780740127 / 1000000000000), (-1845599698387 / 1000000000000)], ![(-266293866199 / 500000000000), (10899046003 / 250000000000), (-53258849941 / 100000000000), (0 / 1), (0 / 1)], ![(-2532362555461 / 1000000000000), (-79136342081 / 31250000000), (0 / 1), (0 / 1), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(0 / 1), (-115349751777 / 62500000000), (8342381719 / 6250000000), (41711898129 / 31250000000), (-922799849193 / 500000000000)], ![(-532587732397 / 1000000000000), (43596184013 / 1000000000000), (-532588499409 / 1000000000000), (0 / 1), (0 / 1)], ![(-126618127773 / 50000000000), (-2532362946591 / 1000000000000), (0 / 1), (0 / 1), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 37) : ℤ :=
  ([8, 2, 3, 3, 2, 8] : List ℤ).getD
    ((seed 5 37).splits.idxOf (sourceShape 5 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 37) : ℚ :=
  ([(-4910549986249 / 1000000000000), (-576992815661 / 500000000000), (-1730169979831 / 1000000000000), (-1730169938861 / 1000000000000), (-57699284377 / 50000000000), (-613818434307 / 125000000000)] : List ℚ).getD
    ((seed 5 37).splits.idxOf (sourceShape 5 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 37) : ℚ :=
  ([(-613818748281 / 125000000000), (-1153985631321 / 1000000000000), (-173016997983 / 100000000000), (-86508496943 / 50000000000), (-1153985687539 / 1000000000000), (-982109494891 / 200000000000)] : List ℚ).getD
    ((seed 5 37).splits.idxOf (sourceShape 5 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 37) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 37 =>
        (splitWeight 5 37 0 c : ℝ) / 1000000000000) ≤
          (1 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 37, ∏ i, weights i (c.val i) ≤ 1 := by
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
