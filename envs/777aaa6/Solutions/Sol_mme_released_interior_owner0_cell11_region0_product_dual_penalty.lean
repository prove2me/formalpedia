-- Prove2me | solution 1 for mme_released_interior_owner0_cell11_region0_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T12:25:05.528013+00:00
-- url     : https://prove2.me/submissions/553c4872-cb37-4d48-9134-846ed199f914

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 11) : ℚ :=
  (splitWeight 0 11 0 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(13458356658000000000000000000000000 / 176183792600638248545343112852033729), (148041735851500000000000000000000000 / 1938021718607020733998774241372371019), (1 / 1), (1 / 1), (1 / 1)], ![(114806852131 / 200000000000), (1064177541451 / 1000000000000), (574032849453 / 1000000000000), (1 / 1), (1 / 1)], ![(1 / 1), (150140240819 / 1000000000000), (985730646593 / 250000000000), (157716688917 / 40000000000), (75070155881 / 500000000000)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![4, 4, 0, 0, 0], ![1, 0, 1, 0, 0], ![0, 3, -1, -1, 3]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-1285963750163 / 500000000000), (-2571928766093 / 1000000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-138766549223 / 250000000000), (12440447853 / 200000000000), (-69383581911 / 125000000000), (0 / 1), (0 / 1)], ![(0 / 1), (-474046370719 / 250000000000), (685961110761 / 500000000000), (1097536689 / 800000000), (-379237002073 / 200000000000)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-102877100013 / 40000000000), (-642982191523 / 250000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-555066196891 / 1000000000000), (31101119633 / 500000000000), (-555068655287 / 1000000000000), (0 / 1), (0 / 1)], ![(0 / 1), (-15169483863 / 8000000000), (1371922221523 / 1000000000000), (1371920861251 / 1000000000000), (-474046252591 / 250000000000)]]

private def alphaScale (c : MME.ReleasedInterior.Split 11) : ℤ :=
  ([8, 2, 3, 3, 2, 8] : List ℤ).getD
    ((seed 0 11).splits.idxOf (sourceShape 0 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 11) : ℚ :=
  ([(-5023178707663 / 1000000000000), (-17778193747 / 15625000000), (-1755073934089 / 1000000000000), (-877537050867 / 500000000000), (-568902152653 / 500000000000), (-2511591452167 / 500000000000)] : List ℚ).getD
    ((seed 0 11).splits.idxOf (sourceShape 0 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 11) : ℚ :=
  ([(-2511589353831 / 500000000000), (-1137804399807 / 1000000000000), (-219384241761 / 125000000000), (-1755074101733 / 1000000000000), (-227560861061 / 200000000000), (-5023182904333 / 1000000000000)] : List ℚ).getD
    ((seed 0 11).splits.idxOf (sourceShape 0 c)) 0

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
        (splitWeight 0 11 0 c : ℝ) / 1000000000000) ≤
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
