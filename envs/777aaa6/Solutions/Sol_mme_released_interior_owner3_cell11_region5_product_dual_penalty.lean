-- Prove2me | solution 1 for mme_released_interior_owner3_cell11_region5_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T16:05:40.438148+00:00
-- url     : https://prove2.me/submissions/0b163d1c-cd1a-48d1-8fb2-0b699d95286e

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 11) : ℚ :=
  (splitWeight 3 11 5 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(592454236731 / 1000000000000), (296227883561 / 500000000000), (1 / 1), (1 / 1), (1 / 1)], ![(286752114609 / 500000000000), (1067100681609 / 1000000000000), (573507182501 / 1000000000000), (1 / 1), (1 / 1)], ![(1 / 1), (10043070227200000000000000000000000 / 516354343988601941426225618336628067), (786321716364200000000000000000000000 / 1549063031965805824278676855009884201), (262107962027200000000000000000000000 / 516354343988601941426225618336628067), (30129172568000000000000000000000000 / 1549063031965805824278676855009884201)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![1, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![0, 6, 1, 1, 6]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-523481646541 / 1000000000000), (-523479063407 / 1000000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-555989968041 / 1000000000000), (64945327389 / 1000000000000), (-277992409257 / 500000000000), (0 / 1), (0 / 1)], ![(0 / 1), (-49248879699 / 12500000000), (-67803951459 / 100000000000), (-678036755269 / 1000000000000), (-1969955820463 / 500000000000)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-26174082327 / 50000000000), (-261739531703 / 500000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-13899749201 / 25000000000), (6494532739 / 100000000000), (-555984818513 / 1000000000000), (0 / 1), (0 / 1)], ![(0 / 1), (-3939910375919 / 1000000000000), (-678039514589 / 1000000000000), (-169509188817 / 250000000000), (-157596465637 / 40000000000)]]

private def alphaScale (c : MME.ReleasedInterior.Split 11) : ℤ :=
  ([8, 3, 2, 2, 3, 8] : List ℤ).getD
    ((seed 3 11).splits.idxOf (sourceShape 3 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 11) : ℚ :=
  ([(-2509687128951 / 500000000000), (-351501195929 / 200000000000), (-71035828163 / 62500000000), (-71035817151 / 62500000000), (-878752893359 / 500000000000), (-5019383255529 / 1000000000000)] : List ℚ).getD
    ((seed 3 11).splits.idxOf (sourceShape 3 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 11) : ℚ :=
  ([(-5019374257901 / 1000000000000), (-439376494911 / 250000000000), (-1136573250607 / 1000000000000), (-227314614883 / 200000000000), (-1757505786717 / 1000000000000), (-627422906941 / 125000000000)] : List ℚ).getD
    ((seed 3 11).splits.idxOf (sourceShape 3 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 11) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 11 =>
        (splitWeight 3 11 5 c : ℝ) / 1000000000000) ≤
          (1 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 11, ∏ i, weights i (c.val i) ≤ 1 := by
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
