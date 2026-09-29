-- Prove2me | solution 1 for mme_released_interior_owner1_cell15_region3_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T12:44:40.410426+00:00
-- url     : https://prove2.me/submissions/97f36bb3-fa88-422b-a1ad-eda911dd172b

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 15) : ℚ :=
  (splitWeight 1 15 3 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(851766658552000000000000000000000000 / 3745746015310004414636446174884456381), (851259333547000000000000000000000000 / 3745746015310004414636446174884456381), (1 / 1), (1 / 1), (1 / 1)], ![(1 / 1), (1 / 1), (604372228767 / 1000000000000), (1977413927251 / 1000000000000), (302162707711 / 500000000000)], ![(21298529817 / 25000000000), (851906293401 / 1000000000000), (1 / 1), (1 / 1), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![3, 3, 0, 0, 0], ![0, 0, 1, 0, 1], ![1, 1, 0, 0, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-740531732377 / 500000000000), (-1481659257211 / 1000000000000), (0 / 1), (0 / 1), (0 / 1)], ![(0 / 1), (0 / 1), (-503564998073 / 1000000000000), (681789893669 / 1000000000000), (-125910614719 / 250000000000)], ![(-40059444303 / 250000000000), (-160278742473 / 1000000000000), (0 / 1), (0 / 1), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-1481063464753 / 1000000000000), (-148165925721 / 100000000000), (0 / 1), (0 / 1), (0 / 1)], ![(0 / 1), (0 / 1), (-62945624759 / 125000000000), (68178989367 / 100000000000), (-4029139671 / 8000000000)], ![(-160237777211 / 1000000000000), (-20034842809 / 125000000000), (0 / 1), (0 / 1), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 15) : ℤ :=
  ([4, 2, 2, 4] : List ℤ).getD
    ((seed 1 15).splits.idxOf (sourceShape 1 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 15) : ℚ :=
  ([(-2144943700839 / 1000000000000), (-239888078389 / 250000000000), (-60006696297 / 62500000000), (-1072751498879 / 500000000000)] : List ℚ).getD
    ((seed 1 15).splits.idxOf (sourceShape 1 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 15) : ℚ :=
  ([(-1072471850419 / 500000000000), (-191910462711 / 200000000000), (-960107140751 / 1000000000000), (-2145502997757 / 1000000000000)] : List ℚ).getD
    ((seed 1 15).splits.idxOf (sourceShape 1 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 15) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 15 =>
        (splitWeight 1 15 3 c : ℝ) / 1000000000000) ≤
          (1 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 15, ∏ i, weights i (c.val i) ≤ 1 := by
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
