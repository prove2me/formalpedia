-- Prove2me | solution 1 for mme_released_interior_owner3_cell10_region4_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T16:05:34.843185+00:00
-- url     : https://prove2.me/submissions/b6f2935b-786d-4adc-8ae6-069a53441aea

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 10) : ℚ :=
  (splitWeight 3 10 4 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(212664892891 / 250000000000), (42529433367 / 50000000000), (1 / 1), (1 / 1), (1 / 1)], ![(106316931509 / 125000000000), (849565711859 / 1000000000000), (1 / 1), (1 / 1), (1 / 1)], ![(1 / 1), (1 / 1), (149363806901250000000000000000000000 / 944688939971273521803363328623310711), (503890074844500000000000000000000000 / 944688939971273521803363328623310711), (149346909624250000000000000000000000 / 944688939971273521803363328623310711)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![1, 1, 0, 0, 0], ![1, 1, 0, 0, 0], ![0, 0, 3, 1, 3]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-161743263859 / 1000000000000), (-40456654847 / 250000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-32377836843 / 200000000000), (-163029987291 / 1000000000000), (0 / 1), (0 / 1), (0 / 1)], ![(0 / 1), (0 / 1), (-1844470722257 / 1000000000000), (-628497570441 / 1000000000000), (-1844583856979 / 1000000000000)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-80871631929 / 500000000000), (-161826619387 / 1000000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-80944592107 / 500000000000), (-16302998729 / 100000000000), (0 / 1), (0 / 1), (0 / 1)], ![(0 / 1), (0 / 1), (-115279420141 / 62500000000), (-15712439261 / 25000000000), (-922291928489 / 500000000000)]]

private def alphaScale (c : MME.ReleasedInterior.Split 10) : ℤ :=
  ([4, 2, 2, 4] : List ℤ).getD
    ((seed 3 10).splits.idxOf (sourceShape 3 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 10) : ℚ :=
  ([(-2169327328933 / 1000000000000), (-953270821589 / 1000000000000), (-238053343511 / 250000000000), (-433643261011 / 200000000000)] : List ℚ).getD
    ((seed 3 10).splits.idxOf (sourceShape 3 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 10) : ℚ :=
  ([(-542331832233 / 250000000000), (-238317705397 / 250000000000), (-952213374043 / 1000000000000), (-1084108152527 / 500000000000)] : List ℚ).getD
    ((seed 3 10).splits.idxOf (sourceShape 3 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 10) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 10 =>
        (splitWeight 3 10 4 c : ℝ) / 1000000000000) ≤
          (1 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 10, ∏ i, weights i (c.val i) ≤ 1 := by
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
