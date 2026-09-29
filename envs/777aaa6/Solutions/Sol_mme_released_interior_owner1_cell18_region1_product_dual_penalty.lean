-- Prove2me | solution 1 for mme_released_interior_owner1_cell18_region1_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T13:17:15.938068+00:00
-- url     : https://prove2.me/submissions/66de70e2-b98f-4e18-bf8d-6a733a7cd4a7

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 18) : ℚ :=
  (splitWeight 1 18 1 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(52136155667000000000000000000000000 / 704009674629592293271286186607020693), (13861532830000000000000000000000000 / 100572810661370327610183740943860099), (52135621611000000000000000000000000 / 704009674629592293271286186607020693), (1 / 1), (1 / 1)], ![(592501842913 / 1000000000000), (118499769459 / 200000000000), (1 / 1), (1 / 1), (1 / 1)], ![(1 / 1), (15071504873 / 100000000000), (786026463589 / 200000000000), (1965055718867 / 500000000000), (18839340871 / 125000000000)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![4, 3, 4, 0, 0], ![1, 1, 0, 0, 0], ![0, 3, -1, -1, 3]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-2602933423623 / 1000000000000), (-1981764367939 / 1000000000000), (-1301471833581 / 500000000000), (0 / 1), (0 / 1)], ![(-523401295577 / 1000000000000), (-523406351469 / 1000000000000), (0 / 1), (0 / 1), (0 / 1)], ![(0 / 1), (-1892364319477 / 1000000000000), (684336547001 / 500000000000), (85541736321 / 62500000000), (-946183227191 / 500000000000)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-1301466711811 / 500000000000), (-990882183969 / 500000000000), (-2602943667161 / 1000000000000), (0 / 1), (0 / 1)], ![(-20936051823 / 40000000000), (-130851587867 / 250000000000), (0 / 1), (0 / 1), (0 / 1)], ![(0 / 1), (-473091079869 / 250000000000), (1368673094003 / 1000000000000), (1368667781137 / 1000000000000), (-1892366454381 / 1000000000000)]]

private def alphaScale (c : MME.ReleasedInterior.Split 18) : ℤ :=
  ([3, 8, 2, 2, 8, 3] : List ℤ).getD
    ((seed 1 18).splits.idxOf (sourceShape 1 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 18) : ℚ :=
  ([(-1757671993957 / 1000000000000), (-250935058681 / 50000000000), (-568248812701 / 500000000000), (-1136497882377 / 1000000000000), (-5018714338163 / 1000000000000), (-351534373747 / 200000000000)] : List ℚ).getD
    ((seed 1 18).splits.idxOf (sourceShape 1 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 18) : ℚ :=
  ([(-439417998489 / 250000000000), (-5018701173619 / 1000000000000), (-1136497625401 / 1000000000000), (-142062235297 / 125000000000), (-2509357169081 / 500000000000), (-878835934367 / 500000000000)] : List ℚ).getD
    ((seed 1 18).splits.idxOf (sourceShape 1 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 18) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 18 =>
        (splitWeight 1 18 1 c : ℝ) / 1000000000000) ≤
          (1 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 18, ∏ i, weights i (c.val i) ≤ 1 := by
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
