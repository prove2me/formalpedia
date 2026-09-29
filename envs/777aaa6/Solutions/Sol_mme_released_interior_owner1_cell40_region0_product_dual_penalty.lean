-- Prove2me | solution 1 for mme_released_interior_owner1_cell40_region0_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T15:25:35.553434+00:00
-- url     : https://prove2.me/submissions/25dbcf8b-988c-45cd-b5a3-b1b4db175bbe

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 40) : ℚ :=
  (splitWeight 1 40 0 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(1 / 1), (1 / 1), (1268806090850000000000000000000000 / 7787385830709137941473127528243843), (12253632427193750000000000000000000 / 23362157492127413824419382584731529), (3806450668043750000000000000000000 / 23362157492127413824419382584731529)], ![(852789209609 / 1000000000000), (852853449877 / 1000000000000), (1 / 1), (1 / 1), (1 / 1)], ![(852857185819 / 1000000000000), (426431017911 / 500000000000), (1 / 1), (1 / 1), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![0, 0, 3, 1, 3], ![1, 1, 0, 0, 0], ![1, 1, 0, 0, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(0 / 1), (0 / 1), (-113401803191 / 62500000000), (-645295094387 / 1000000000000), (-1814420340337 / 1000000000000)], ![(-159242878549 / 1000000000000), (-39791887947 / 250000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-159163171277 / 1000000000000), (-159157484523 / 1000000000000), (0 / 1), (0 / 1), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(0 / 1), (0 / 1), (-362885770211 / 200000000000), (-322647547193 / 500000000000), (-113401271271 / 62500000000)], ![(-39810719637 / 250000000000), (-159167551787 / 1000000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-39790792819 / 250000000000), (-79578742261 / 500000000000), (0 / 1), (0 / 1), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 40) : ℤ :=
  ([4, 2, 2, 4] : List ℤ).getD
    ((seed 1 40).splits.idxOf (sourceShape 1 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 40) : ℚ :=
  ([(-533188471841 / 250000000000), (-963625817451 / 1000000000000), (-481847728729 / 500000000000), (-2132826390163 / 1000000000000)] : List ℚ).getD
    ((seed 1 40).splits.idxOf (sourceShape 1 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 40) : ℚ :=
  ([(-2132753887363 / 1000000000000), (-19272516349 / 20000000000), (-963695457457 / 1000000000000), (-1066413195081 / 500000000000)] : List ℚ).getD
    ((seed 1 40).splits.idxOf (sourceShape 1 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 40) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 40 =>
        (splitWeight 1 40 0 c : ℝ) / 1000000000000) ≤
          (1 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 40, ∏ i, weights i (c.val i) ≤ 1 := by
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
