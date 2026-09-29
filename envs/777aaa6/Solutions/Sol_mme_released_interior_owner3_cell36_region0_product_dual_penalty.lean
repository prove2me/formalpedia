-- Prove2me | solution 1 for mme_released_interior_owner3_cell36_region0_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-24T09:13:04.818773+00:00
-- url     : https://prove2.me/submissions/d1b4e269-ddc3-40d0-972c-fde89b14321e

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 36) : ℚ :=
  (splitWeight 3 36 0 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(1 / 1), (157106032841 / 1000000000000), (3812474685883 / 1000000000000), (238276860441 / 62500000000), (78553016911 / 500000000000)], ![(119790283949 / 200000000000), (598944777737 / 1000000000000), (1 / 1), (1 / 1), (1 / 1)], ![(36523550049625000000000000000000000 / 473568106626540769619154007136632157), (65667034491750000000000000000000000 / 473568106626540769619154007136632157), (36522735359250000000000000000000000 / 473568106626540769619154007136632157), (1 / 1), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![0, 3, -1, -1, 3], ![1, 1, 0, 0, 0], ![4, 3, 4, 0, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(0 / 1), (-1850834333179 / 1000000000000), (1338278502143 / 1000000000000), (167283340001 / 125000000000), (-370166865387 / 200000000000)], ![(-256287393209 / 500000000000), (-512585875873 / 1000000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-512467695901 / 200000000000), (-123481168589 / 62500000000), (-1281180392823 / 500000000000), (0 / 1), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(0 / 1), (-925417166589 / 500000000000), (5227650399 / 3906250000), (1338266720009 / 1000000000000), (-925417163467 / 500000000000)], ![(-512574786417 / 1000000000000), (-16018308621 / 31250000000), (0 / 1), (0 / 1), (0 / 1)], ![(-160146154969 / 62500000000), (-1975698697423 / 1000000000000), (-512472157129 / 200000000000), (0 / 1), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 36) : ℤ :=
  ([3, 8, 2, 2, 8, 3] : List ℤ).getD
    ((seed 3 36).splits.idxOf (sourceShape 3 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 36) : ℚ :=
  ([(-217082204421 / 125000000000), (-2462873796399 / 500000000000), (-230001214231 / 200000000000), (-575003381917 / 500000000000), (-985156198953 / 200000000000), (-1736657069919 / 1000000000000)] : List ℚ).getD
    ((seed 3 36).splits.idxOf (sourceShape 3 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 36) : ℚ :=
  ([(-1736657635367 / 1000000000000), (-4925747592797 / 1000000000000), (-575003035577 / 500000000000), (-1150006763833 / 1000000000000), (-1231445248691 / 250000000000), (-868328534959 / 500000000000)] : List ℚ).getD
    ((seed 3 36).splits.idxOf (sourceShape 3 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 36) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 36 =>
        (splitWeight 3 36 0 c : ℝ) / 1000000000000) ≤
          (1 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 36, ∏ i, weights i (c.val i) ≤ 1 := by
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
