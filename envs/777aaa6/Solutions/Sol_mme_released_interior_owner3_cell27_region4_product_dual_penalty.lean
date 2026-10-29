-- Prove2me | solution 1 for mme_released_interior_owner3_cell27_region4_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T00:31:19.712774+00:00
-- url     : https://prove2.me/submissions/d2a3b5ea-b5ab-42c3-84d9-a459856b3359

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 27) : ℚ :=
  (splitWeight 3 27 4 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(27967498232861 / 500000000000000), (743275484941441 / 1000000000000000), (743275289645821 / 1000000000000000), (55935568068451 / 1000000000000000), (1 / 1)], ![(11689495042729 / 250000000000000), (84830548137811 / 125000000000000), (339322356089921 / 500000000000000), (2922337535181 / 62500000000000), (1 / 1)], ![(160028683259537 / 500000000000000), (310909429504761 / 500000000000000), (80014366211707 / 250000000000000), (1 / 1), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![4, 0, 0, 4, 0], ![4, 1, 1, 4, 0], ![2, 1, 2, 0, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-576713007973739 / 200000000000000), (-14834426458659 / 50000000000000), (-74172197980799 / 250000000000000), (-2883554820867273 / 1000000000000000), (0 / 1)], ![(-306277033897171 / 100000000000000), (-387658021900199 / 1000000000000000), (-1938287699717 / 5000000000000), (-612556546993017 / 200000000000000), (0 / 1)], ![(-1139255028883273 / 1000000000000000), (-59388306514263 / 125000000000000), (-284813680416041 / 250000000000000), (0 / 1), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-288356503986869 / 100000000000000), (-296688529173179 / 1000000000000000), (-59337758384639 / 200000000000000), (-2883554820867269 / 1000000000000000), (0 / 1)], ![(-1531385169485853 / 500000000000000), (-387658021900197 / 1000000000000000), (-193828769971699 / 500000000000000), (-76569568374127 / 25000000000000), (0 / 1)], ![(-113925502888327 / 100000000000000), (-475106452114103 / 1000000000000000), (-1139254721664161 / 1000000000000000), (0 / 1), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 27) : ℤ :=
  ([6, 3, 6, 9, 2, 2, 9, 6, 3, 6] : List ℤ).getD
    ((seed 3 27).splits.idxOf (sourceShape 3 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 27) : ℚ :=
  ([(-2250409382242281 / 500000000000000), (-911656682471851 / 500000000000000), (-4412383458781393 / 1000000000000000), (-6407258774774703 / 1000000000000000), (-289881663237929 / 250000000000000), (-1159527395851523 / 1000000000000000), (-6407236124475073 / 1000000000000000), (-2206196429261471 / 500000000000000), (-911656638478359 / 500000000000000), (-2250403175290529 / 500000000000000)] : List ℚ).getD
    ((seed 3 27).splits.idxOf (sourceShape 3 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 27) : ℚ :=
  ([(-1125204691121139 / 250000000000000), (-911656682471849 / 500000000000000), (-4412383458781387 / 1000000000000000), (-1281451754954939 / 200000000000000), (-1159526652951713 / 1000000000000000), (-905880778009 / 781250000000), (-800904515559383 / 125000000000000), (-4412392858522937 / 1000000000000000), (-364662655391343 / 200000000000000), (-1125201587645263 / 250000000000000)] : List ℚ).getD
    ((seed 3 27).splits.idxOf (sourceShape 3 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_nonneg : ∀ c, 0 ≤ alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 27) (hc : 0 < alphaQ c) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) hc
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c hc; decide +kernel

theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 27 =>
        (splitWeight 3 27 4 c : ℝ) / 1000000000000) ≤
          (440 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 27, ∏ i, weights i (c.val i) ≤ 1 := by
    decide +kernel
  have h := mme_rational_product_dual_penalty_certificate alphaQ
    alpha_nonneg hprob weights weights_pos hmass weightLower alphaUpper
    (fun i j => (weight_logs i j).1) (fun c hc => (alpha_logs c hc).2)
    (440 / 1000000000)
  have hbound : Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c => (alphaQ c : ℝ)) ≤ ((440 / 1000000000 : ℚ) : ℝ) := by
    apply h
    decide +kernel
  simpa only [alphaQ, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat,
    Rat.cast_one, Rat.cast_zero] using hbound
