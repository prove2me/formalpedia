-- Prove2me | solution 1 for mme_released_interior_owner4_cell25_region1_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-24T17:17:45.136366+00:00
-- url     : https://prove2.me/submissions/8d67ab42-7104-4973-89ff-6a21e6eee6bb

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 25) : ℚ :=
  (splitWeight 4 25 1 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(279526341867 / 1000000000000), (1400635333489 / 1000000000000), (1400593414011 / 1000000000000), (279489463011 / 1000000000000), (1 / 1)], ![(97870103807500000000000000000000000 / 4434728040403984667778937734313985141), (97867106537750000000000000000000000 / 4434728040403984667778937734313985141), (1 / 1), (1 / 1), (1 / 1)], ![(5320053363 / 100000000000), (397109549069 / 200000000000), (6891910845507 / 500000000000), (1985415387389 / 1000000000000), (53200385533 / 1000000000000)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![2, 0, 0, 2, 0], ![6, 6, 0, 0, 0], ![5, 0, -3, 0, 5]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-254931748887 / 200000000000), (67385188663 / 200000000000), (67379202793 / 200000000000), (-637395343261 / 500000000000), (0 / 1)], ![(-3813580443543 / 1000000000000), (-381361106899 / 100000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-1466843426023 / 500000000000), (685894818313 / 1000000000000), (1311747781601 / 500000000000), (342914077707 / 500000000000), (-14668448179 / 5000000000)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-637329372217 / 500000000000), (84231485829 / 250000000000), (168448006983 / 500000000000), (-1274790686521 / 1000000000000), (0 / 1)], ![(-1906790221771 / 500000000000), (-3813611068989 / 1000000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-586737370409 / 200000000000), (342947409157 / 500000000000), (2623495563203 / 1000000000000), (137165631083 / 200000000000), (-2933689635799 / 1000000000000)]]

private def alphaScale (c : MME.ReleasedInterior.Split 25) : ℤ :=
  ([7, 2, 5, 12, 12, 5, 2, 7] : List ℤ).getD
    ((seed 4 25).splits.idxOf (sourceShape 4 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 25) : ℚ :=
  ([(-550309538969 / 125000000000), (-106648608297 / 125000000000), (-1395413172409 / 500000000000), (-8021928824409 / 1000000000000), (-1604417721227 / 200000000000), (-558164047341 / 200000000000), (-853189562471 / 1000000000000), (-4402441657999 / 1000000000000)] : List ℚ).getD
    ((seed 4 25).splits.idxOf (sourceShape 4 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 25) : ℚ :=
  ([(-4402476311751 / 1000000000000), (-6825510931 / 8000000000), (-2790826344817 / 1000000000000), (-1002741103051 / 125000000000), (-4011044303067 / 500000000000), (-87213132397 / 31250000000), (-85318956247 / 100000000000), (-2201220828999 / 500000000000)] : List ℚ).getD
    ((seed 4 25).splits.idxOf (sourceShape 4 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 25) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 25 =>
        (splitWeight 4 25 1 c : ℝ) / 1000000000000) ≤
          (1 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 25, ∏ i, weights i (c.val i) ≤ 1 := by
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
