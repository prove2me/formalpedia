-- Prove2me | solution 1 for mme_released_interior_owner3_cell21_region4_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T00:12:55.04221+00:00
-- url     : https://prove2.me/submissions/230eeae5-456f-4c42-b9a0-857be7d6a12c

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 21) : ℚ :=
  (splitWeight 3 21 4 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(48914054519687 / 125000000000000), (185623323308289 / 250000000000000), (195656210407361 / 500000000000000), (1 / 1), (1 / 1)], ![(2699535229697 / 1000000000000000), (40096553473127 / 250000000000000), (296266312174529 / 250000000000000), (32077240745747 / 200000000000000), (1349768144087 / 500000000000000)], ![(311207014463711 / 1000000000000000), (633154355996327 / 1000000000000000), (7780175711619 / 25000000000000), (1 / 1), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![1, 0, 1, 0, 0], ![9, 3, 0, 3, 9], ![2, 1, 2, 0, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-938248968626289 / 1000000000000000), (-37217680128587 / 125000000000000), (-938249007834791 / 1000000000000000), (0 / 1), (0 / 1)], ![(-369667228621151 / 62500000000000), (-457542633886141 / 250000000000000), (16979783526373 / 100000000000000), (-1830170598915181 / 1000000000000000), (-5914675265842481 / 1000000000000000)], ![(-7295605918009 / 6250000000000), (-91408207645741 / 200000000000000), (-1167296901891937 / 1000000000000000), (0 / 1), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-938248968626287 / 1000000000000000), (-59548288205739 / 200000000000000), (-938249007834789 / 1000000000000000), (0 / 1), (0 / 1)], ![(-739334457242301 / 125000000000000), (-22877131694307 / 12500000000000), (169797835263731 / 1000000000000000), (-1830170598915177 / 1000000000000000), (-739334408230309 / 125000000000000)], ![(-1167296946881437 / 1000000000000000), (-457041038228703 / 1000000000000000), (-233459380378387 / 200000000000000), (0 / 1), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 21) : ℤ :=
  ([12, 5, 3, 5, 1, 5, 3, 5, 12] : List ℤ).getD
    ((seed 3 21).splits.idxOf (sourceShape 3 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 21) : ℚ :=
  ([(-1002527647668761 / 125000000000000), (-659041798075099 / 200000000000000), (-967874059270407 / 500000000000000), (-403182575307397 / 125000000000000), (-58498464399367 / 100000000000000), (-1612730292459529 / 500000000000000), (-1935748036166179 / 1000000000000000), (-3295208874915019 / 1000000000000000), (-50126384797907 / 6250000000000)] : List ℚ).getD
    ((seed 3 21).splits.idxOf (sourceShape 3 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 21) : ℚ :=
  ([(-8020221181350077 / 1000000000000000), (-329520899037549 / 100000000000000), (-1935748118540811 / 1000000000000000), (-3225460602459171 / 1000000000000000), (-146246160998417 / 250000000000000), (-3225460584919053 / 1000000000000000), (-60492126130193 / 31250000000000), (-1647604437457507 / 500000000000000), (-8020221567665109 / 1000000000000000)] : List ℚ).getD
    ((seed 3 21).splits.idxOf (sourceShape 3 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_nonneg : ∀ c, 0 ≤ alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 21) (hc : 0 < alphaQ c) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) hc
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c hc; decide +kernel

theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 21 =>
        (splitWeight 3 21 4 c : ℝ) / 1000000000000) ≤
          (1 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 21, ∏ i, weights i (c.val i) ≤ 1 := by
    decide +kernel
  have h := mme_rational_product_dual_penalty_certificate alphaQ
    alpha_nonneg hprob weights weights_pos hmass weightLower alphaUpper
    (fun i j => (weight_logs i j).1) (fun c hc => (alpha_logs c hc).2)
    (1 / 1000000000)
  have hbound : Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c => (alphaQ c : ℝ)) ≤ ((1 / 1000000000 : ℚ) : ℝ) := by
    apply h
    decide +kernel
  simpa only [alphaQ, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat,
    Rat.cast_one, Rat.cast_zero] using hbound
