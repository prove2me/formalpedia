-- Prove2me | solution 1 for mme_released_interior_owner3_cell22_region3_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T00:13:52.086305+00:00
-- url     : https://prove2.me/submissions/c91c7308-d890-4ff2-9b51-6d897ccded4f

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 22) : ℚ :=
  (splitWeight 3 22 3 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(118916616789821 / 250000000000000), (34542223133499 / 40000000000000), (475666435472821 / 1000000000000000), (1 / 1), (1 / 1)], ![(1 / 1), (26878902733501 / 1000000000000000), (334438560081131 / 500000000000000), (133775405355203 / 200000000000000), (26878870011013 / 1000000000000000)], ![(550321189770193 / 1000000000000000), (110064245305603 / 200000000000000), (1 / 1), (1 / 1), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![1, 0, 1, 0, 0], ![0, 5, 1, 1, 5], ![1, 1, 0, 0, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-185759592400093 / 250000000000000), (-73348509719747 / 500000000000000), (-743038436215251 / 1000000000000000), (0 / 1), (0 / 1)], ![(0 / 1), (-3616413585086689 / 1000000000000000), (-100538728153019 / 250000000000000), (-100538763057133 / 250000000000000), (-361641480249159 / 100000000000000)], ![(-149313297451513 / 250000000000000), (-37328320188291 / 62500000000000), (0 / 1), (0 / 1), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-743038369600371 / 1000000000000000), (-146697019439493 / 1000000000000000), (-743038436215249 / 1000000000000000), (0 / 1), (0 / 1)], ![(0 / 1), (-904103396271671 / 250000000000000), (-201077456306037 / 500000000000000), (-402155052228531 / 1000000000000000), (-723282960498317 / 200000000000000)], ![(-11945063796121 / 20000000000000), (-298626561506327 / 500000000000000), (0 / 1), (0 / 1), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 22) : ℤ :=
  ([7, 2, 3, 3, 2, 7] : List ℤ).getD
    ((seed 3 22).splits.idxOf (sourceShape 3 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 22) : ℚ :=
  ([(-4956706361898003 / 1000000000000000), (-286526315368519 / 250000000000000), (-871223269316689 / 500000000000000), (-43561163621039 / 25000000000000), (-35815782970757 / 31250000000000), (-4956705144314587 / 1000000000000000)] : List ℚ).getD
    ((seed 3 22).splits.idxOf (sourceShape 3 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 22) : ℚ :=
  ([(-1239176590474499 / 250000000000000), (-573052630737037 / 500000000000000), (-871223269316687 / 500000000000000), (-435611636210389 / 250000000000000), (-573052527532111 / 500000000000000), (-4956705144314581 / 1000000000000000)] : List ℚ).getD
    ((seed 3 22).splits.idxOf (sourceShape 3 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_nonneg : ∀ c, 0 ≤ alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 22) (hc : 0 < alphaQ c) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) hc
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c hc; decide +kernel

theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 22 =>
        (splitWeight 3 22 3 c : ℝ) / 1000000000000) ≤
          (1 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 22, ∏ i, weights i (c.val i) ≤ 1 := by
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
