-- Prove2me | solution 1 for mme_released_interior_owner0_cell19_region0_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T12:25:23.446293+00:00
-- url     : https://prove2.me/submissions/71d1f9ce-e016-4c77-b62e-e4f490fb9371

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 19) : ℚ :=
  (splitWeight 0 19 0 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(408645685488000000000000000000000000 / 20261484241340146425583927873445574887), (803035477479000000000000000000000000 / 20261484241340146425583927873445574887), (408651632867000000000000000000000000 / 20261484241340146425583927873445574887), (1 / 1), (1 / 1)], ![(8206761393 / 20000000000), (796916451639 / 1000000000000), (51293004977 / 125000000000), (1 / 1), (1 / 1)], ![(38722649497 / 1000000000000), (2256904051621 / 1000000000000), (8864312001127 / 500000000000), (225693713109 / 100000000000), (2420167711 / 62500000000)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![6, 5, 6, 0, 0], ![2, 1, 2, 0, 0], ![5, -1, -4, -1, 5]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-975907137217 / 250000000000), (-3228078140671 / 1000000000000), (-3903613995097 / 1000000000000), (0 / 1), (0 / 1)], ![(-35630955957 / 40000000000), (-113502717123 / 500000000000), (-890759349647 / 1000000000000), (0 / 1), (0 / 1)], ![(-3251330591823 / 1000000000000), (162798797093 / 200000000000), (718795127157 / 250000000000), (814008642369 / 1000000000000), (-3251329716909 / 1000000000000)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-3903628548867 / 1000000000000), (-322807814067 / 100000000000), (-487951749387 / 125000000000), (0 / 1), (0 / 1)], ![(-222693474731 / 250000000000), (-45401086849 / 200000000000), (-445379674823 / 500000000000), (0 / 1), (0 / 1)], ![(-1625665295911 / 500000000000), (406996992733 / 500000000000), (2875180508629 / 1000000000000), (81400864237 / 100000000000), (-812832429227 / 250000000000)]]

private def alphaScale (c : MME.ReleasedInterior.Split 19) : ℤ :=
  ([12, 5, 3, 5, 1, 5, 3, 5, 12] : List ℤ).getD
    ((seed 0 19).splits.idxOf (sourceShape 0 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 19) : ℚ :=
  ([(-1609146433063 / 200000000000), (-414578167549 / 125000000000), (-119950461873 / 62500000000), (-132193735903 / 40000000000), (-579903066287 / 1000000000000), (-3304843504509 / 1000000000000), (-1919207385313 / 1000000000000), (-331662544421 / 100000000000), (-2011425984533 / 250000000000)] : List ℚ).getD
    ((seed 0 19).splits.idxOf (sourceShape 0 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 19) : ℚ :=
  ([(-4022866082657 / 500000000000), (-3316625340391 / 1000000000000), (-1919207389967 / 1000000000000), (-1652421698787 / 500000000000), (-289951533143 / 500000000000), (-826210876127 / 250000000000), (-59975230791 / 31250000000), (-3316625444209 / 1000000000000), (-8045703938131 / 1000000000000)] : List ℚ).getD
    ((seed 0 19).splits.idxOf (sourceShape 0 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 19) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 19 =>
        (splitWeight 0 19 0 c : ℝ) / 1000000000000) ≤
          (1 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 19, ∏ i, weights i (c.val i) ≤ 1 := by
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
