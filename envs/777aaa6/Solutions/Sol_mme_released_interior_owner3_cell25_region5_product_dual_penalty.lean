-- Prove2me | solution 1 for mme_released_interior_owner3_cell25_region5_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T00:15:14.531209+00:00
-- url     : https://prove2.me/submissions/860b5f93-7c37-47db-ad7c-3aa70d81aefb

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 25) : ℚ :=
  (splitWeight 3 25 5 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(9464410857621 / 50000000000000), (948575898335307 / 1000000000000000), (948575755843217 / 1000000000000000), (189288626456909 / 1000000000000000), (1 / 1)], ![(1953125110211 / 3906250000000), (1953124889789 / 3906250000000), (1 / 1), (1 / 1), (1 / 1)], ![(3467440740217 / 1000000000000000), (129383320426851 / 1000000000000000), (56144891516921 / 62500000000000), (2021614554117 / 15625000000000), (108358216051 / 31250000000000)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![2, 0, 0, 2, 0], ![1, 1, 0, 0, 0], ![8, 3, 0, 3, 8]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-832242233506259 / 500000000000000), (-52793473477599 / 1000000000000000), (-52793623694467 / 1000000000000000), (-166448230468011 / 100000000000000), (0 / 1)], ![(-173286781032979 / 250000000000000), (-34657361849399 / 50000000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-5664338495981313 / 1000000000000000), (-2044975804552389 / 1000000000000000), (-26807714728639 / 250000000000000), (-2044975719250539 / 1000000000000000), (-2832166050626121 / 500000000000000)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-332896893402503 / 200000000000000), (-26396736738799 / 500000000000000), (-26396811847233 / 500000000000000), (-1664482304680107 / 1000000000000000), (0 / 1)], ![(-346573562065957 / 500000000000000), (-346573618493989 / 500000000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-2832169247990653 / 500000000000000), (-408995160910477 / 200000000000000), (-21446171782911 / 200000000000000), (-255621964906317 / 125000000000000), (-1132866420250447 / 200000000000000)]]

private def alphaScale (c : MME.ReleasedInterior.Split 25) : ℤ :=
  ([12, 4, 6, 1, 1, 6, 4, 12] : List ℤ).getD
    ((seed 3 25).splits.idxOf (sourceShape 3 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 25) : ℚ :=
  ([(-4010984018824723 / 500000000000000), (-174432291577177 / 62500000000000), (-4402605233364409 / 1000000000000000), (-426585784690067 / 500000000000000), (-426585803370469 / 500000000000000), (-880521484650207 / 200000000000000), (-558183263372011 / 200000000000000), (-401098184619839 / 50000000000000)] : List ℚ).getD
    ((seed 3 25).splits.idxOf (sourceShape 3 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 25) : ℚ :=
  ([(-1604393607529887 / 200000000000000), (-697729166308707 / 250000000000000), (-4402605233364403 / 1000000000000000), (-213292892345033 / 250000000000000), (-106646450842617 / 125000000000000), (-4402607423251029 / 1000000000000000), (-55818326337201 / 20000000000000), (-8021963692396769 / 1000000000000000)] : List ℚ).getD
    ((seed 3 25).splits.idxOf (sourceShape 3 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_nonneg : ∀ c, 0 ≤ alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 25) (hc : 0 < alphaQ c) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) hc
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c hc; decide +kernel

theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 25 =>
        (splitWeight 3 25 5 c : ℝ) / 1000000000000) ≤
          (1 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 25, ∏ i, weights i (c.val i) ≤ 1 := by
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
