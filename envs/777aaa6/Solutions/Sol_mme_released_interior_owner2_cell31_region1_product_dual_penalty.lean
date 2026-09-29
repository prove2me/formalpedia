-- Prove2me | solution 1 for mme_released_interior_owner2_cell31_region1_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T15:44:35.334006+00:00
-- url     : https://prove2.me/submissions/da18ccb9-e685-40d1-a3f8-3fb32c915204

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 31) : ℚ :=
  (splitWeight 2 31 1 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(10682798809 / 200000000000), (2066023884543 / 1000000000000), (3191467245653 / 250000000000), (206591796027 / 100000000000), (26706943967 / 500000000000)], ![(394726270669000000000000000000000000 / 17447088156901896038085334518057457273), (394716727976000000000000000000000000 / 17447088156901896038085334518057457273), (1 / 1), (1 / 1), (1 / 1)], ![(135999973231 / 500000000000), (725611754783 / 500000000000), (1451189091387 / 1000000000000), (271973455111 / 1000000000000), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![5, -1, -3, -1, 5], ![6, 6, 0, 0, 0], ![2, 0, 0, 2, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-2929682506581 / 1000000000000), (181406482849 / 250000000000), (1273387561893 / 500000000000), (145114932091 / 200000000000), (-2929684493159 / 1000000000000)], ![(-11839798459 / 3125000000), (-1894379841321 / 500000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-650976704759 / 500000000000), (186203500167 / 500000000000), (37238328339 / 100000000000), (-1302050808953 / 1000000000000), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-146484125329 / 50000000000), (725625931397 / 1000000000000), (2546775123787 / 1000000000000), (90696832557 / 125000000000), (-1464842246579 / 500000000000)], ![(-3788735506879 / 1000000000000), (-3788759682641 / 1000000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-1301953409517 / 1000000000000), (74481400067 / 200000000000), (372383283391 / 1000000000000), (-162756351119 / 125000000000), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 31) : ℤ :=
  ([7, 2, 4, 12, 12, 4, 2, 7] : List ℤ).getD
    ((seed 2 31).splits.idxOf (sourceShape 2 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 31) : ℚ :=
  ([(-2182580192217 / 500000000000), (-108697137463 / 125000000000), (-2690753846091 / 1000000000000), (-2005093352539 / 250000000000), (-8020492998467 / 1000000000000), (-2690750467861 / 1000000000000), (-21739438963 / 25000000000), (-13641057599 / 3125000000)] : List ℚ).getD
    ((seed 2 31).splits.idxOf (sourceShape 2 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 31) : ℚ :=
  ([(-4365160384433 / 1000000000000), (-869577099703 / 1000000000000), (-269075384609 / 100000000000), (-1604074682031 / 200000000000), (-4010246499233 / 500000000000), (-134537523393 / 50000000000), (-869577558519 / 1000000000000), (-4365138431679 / 1000000000000)] : List ℚ).getD
    ((seed 2 31).splits.idxOf (sourceShape 2 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 31) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 31 =>
        (splitWeight 2 31 1 c : ℝ) / 1000000000000) ≤
          (1 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 31, ∏ i, weights i (c.val i) ≤ 1 := by
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
