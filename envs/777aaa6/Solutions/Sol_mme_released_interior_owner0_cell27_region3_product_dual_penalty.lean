-- Prove2me | solution 1 for mme_released_interior_owner0_cell27_region3_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T12:43:58.662548+00:00
-- url     : https://prove2.me/submissions/3c48b124-e652-4da3-874f-34b00d0c27a2

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 27) : ℚ :=
  (splitWeight 0 27 3 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(7058859196000000000000000000000000 / 634209861485366997018498977822355377), (93800273081480000000000000000000000 / 634209861485366997018498977822355377), (93800480695240000000000000000000000 / 634209861485366997018498977822355377), (7058908689400000000000000000000000 / 634209861485366997018498977822355377), (1 / 1)], ![(10562606611 / 62500000000), (613192068203 / 250000000000), (1226386857187 / 500000000000), (169002907703 / 1000000000000), (1 / 1)], ![(445031856783 / 1000000000000), (1383394769 / 1600000000), (222517055107 / 500000000000), (1 / 1), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![7, 3, 3, 7, 0], ![3, -1, -1, 3, 0], ![2, 1, 2, 0, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-562262057499 / 125000000000), (-477803036037 / 250000000000), (-191120993079 / 100000000000), (-4498089448487 / 1000000000000), (0 / 1)], ![(-1777846470761 / 1000000000000), (448608646981 / 500000000000), (448609756249 / 500000000000), (-111114959929 / 62500000000), (0 / 1)], ![(-404804705551 / 500000000000), (-145463173333 / 1000000000000), (-202401086897 / 250000000000), (0 / 1), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-4498096459991 / 1000000000000), (-1911212144147 / 1000000000000), (-1911209930789 / 1000000000000), (-2249044724243 / 500000000000), (0 / 1)], ![(-44446161769 / 25000000000), (897217293963 / 1000000000000), (897219512499 / 1000000000000), (-1777839358863 / 1000000000000), (0 / 1)], ![(-809609411101 / 1000000000000), (-36365793333 / 250000000000), (-809604347587 / 1000000000000), (0 / 1), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 27) : ℤ :=
  ([7, 10, 3, 2, 7, 7, 2, 3, 10, 7] : List ℤ).getD
    ((seed 0 27).splits.idxOf (sourceShape 0 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 27) : ℚ :=
  ([(-4412396567381 / 1000000000000), (-6407206467623 / 1000000000000), (-911655625233 / 500000000000), (-1159529923601 / 1000000000000), (-112518823231 / 25000000000), (-4500752758799 / 1000000000000), (-579764964479 / 500000000000), (-113956992619 / 62500000000), (-6407206600987 / 1000000000000), (-551549604229 / 125000000000)] : List ℚ).getD
    ((seed 0 27).splits.idxOf (sourceShape 0 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 27) : ℚ :=
  ([(-220619828369 / 50000000000), (-3203603233811 / 500000000000), (-364662250093 / 200000000000), (-2898824809 / 2500000000), (-4500752929239 / 1000000000000), (-2250376379399 / 500000000000), (-1159529928957 / 1000000000000), (-1823311881903 / 1000000000000), (-3203603300493 / 500000000000), (-4412396833831 / 1000000000000)] : List ℚ).getD
    ((seed 0 27).splits.idxOf (sourceShape 0 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 27) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 27 =>
        (splitWeight 0 27 3 c : ℝ) / 1000000000000) ≤
          (439 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 27, ∏ i, weights i (c.val i) ≤ 1 := by
    decide +kernel
  have h := mme_rational_product_dual_penalty_certificate alphaQ
    (fun c => (alpha_pos c).le) hprob weights weights_pos hmass weightLower alphaUpper
    (fun i j => (weight_logs i j).1) (fun c _ => (alpha_logs c).2)
    (439 / 1000000000)
  have hbound : Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c => (alphaQ c : ℝ)) ≤ ((439 / 1000000000 : ℚ) : ℝ) := by
    apply h
    decide +kernel
  simpa only [alphaQ, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat,
    Rat.cast_one, Rat.cast_zero] using hbound


#print axioms solution
