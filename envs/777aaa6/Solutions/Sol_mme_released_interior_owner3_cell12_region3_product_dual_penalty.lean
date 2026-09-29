-- Prove2me | solution 1 for mme_released_interior_owner3_cell12_region3_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T16:05:41.349112+00:00
-- url     : https://prove2.me/submissions/75308aaa-e52d-4d1c-91d1-3dbcc314031d

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 12) : ℚ :=
  (splitWeight 3 12 3 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(195615156557 / 500000000000), (195615092363 / 500000000000), (1 / 1), (1 / 1), (1 / 1)], ![(278377119363 / 1000000000000), (1405158057153 / 1000000000000), (70257882081 / 50000000000), (55675338571 / 200000000000), (1 / 1)], ![(26604160871000000000000000000000000 / 8881374688301751317122140665983980391), (992259552286500000000000000000000000 / 8881374688301751317122140665983980391), (6883684811966000000000000000000000000 / 8881374688301751317122140665983980391), (992258871731500000000000000000000000 / 8881374688301751317122140665983980391), (26604168704000000000000000000000000 / 8881374688301751317122140665983980391)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![2, 2, 0, 0, 0], ![2, 0, 0, 2, 0], ![9, 4, 1, 4, 9]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-469229428157 / 500000000000), (-938459184479 / 1000000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-19980914689 / 15625000000), (85037448163 / 250000000000), (85037374233 / 250000000000), (-63939003611 / 50000000000), (0 / 1)], ![(-581064400397 / 100000000000), (-438345382547 / 200000000000), (-127401130279 / 500000000000), (-2191727598599 / 1000000000000), (-2905321854771 / 500000000000)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-938458856313 / 1000000000000), (-469229592239 / 500000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-255755708019 / 200000000000), (340149792653 / 1000000000000), (340149496933 / 1000000000000), (-1278780072219 / 1000000000000), (0 / 1)], ![(-5810644003969 / 1000000000000), (-1095863456367 / 500000000000), (-254802260557 / 1000000000000), (-1095863799299 / 500000000000), (-5810643709541 / 1000000000000)]]

private def alphaScale (c : MME.ReleasedInterior.Split 12) : ℤ :=
  ([12, 7, 5, 2, 2, 5, 7, 12] : List ℤ).getD
    ((seed 3 12).splits.idxOf (sourceShape 3 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 12) : ℚ :=
  ([(-8027883262069 / 1000000000000), (-551120730157 / 125000000000), (-2790036600273 / 1000000000000), (-853111619939 / 1000000000000), (-853111652383 / 1000000000000), (-2790036662257 / 1000000000000), (-2204482661583 / 500000000000), (-8027881107203 / 1000000000000)] : List ℚ).getD
    ((seed 3 12).splits.idxOf (sourceShape 3 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 12) : ℚ :=
  ([(-2006970815517 / 250000000000), (-881793168251 / 200000000000), (-174377287517 / 62500000000), (-426555809969 / 500000000000), (-426555826191 / 500000000000), (-174377291391 / 62500000000), (-881793064633 / 200000000000), (-4013940553601 / 500000000000)] : List ℚ).getD
    ((seed 3 12).splits.idxOf (sourceShape 3 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 12) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 12 =>
        (splitWeight 3 12 3 c : ℝ) / 1000000000000) ≤
          (1 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 12, ∏ i, weights i (c.val i) ≤ 1 := by
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
