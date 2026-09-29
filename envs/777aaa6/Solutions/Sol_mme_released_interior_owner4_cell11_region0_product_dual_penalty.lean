-- Prove2me | solution 1 for mme_released_interior_owner4_cell11_region0_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-24T09:16:02.250995+00:00
-- url     : https://prove2.me/submissions/540e8abc-d707-4bee-9bd1-c85fb2115d35

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 11) : ℚ :=
  (splitWeight 4 11 0 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(29635925917 / 50000000000), (118542387051 / 200000000000), (1 / 1), (1 / 1), (1 / 1)], ![(114679034174600000000000000000000000 / 1547682456876696168914904895271241139), (213710484643200000000000000000000000 / 1547682456876696168914904895271241139), (114676450087800000000000000000000000 / 1547682456876696168914904895271241139), (1 / 1), (1 / 1)], ![(1 / 1), (37764582007 / 250000000000), (1961506828189 / 500000000000), (3922967406289 / 1000000000000), (151057558351 / 1000000000000)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![1, 1, 0, 0, 0], ![4, 3, 4, 0, 0], ![0, 3, -1, -1, 3]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-523035666641 / 1000000000000), (-523046773299 / 1000000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-650594170707 / 250000000000), (-1979891678331 / 1000000000000), (-650599804073 / 250000000000), (0 / 1), (0 / 1)], ![(0 / 1), (-1890089238423 / 1000000000000), (1366860148327 / 1000000000000), (1366848358829 / 1000000000000), (-945047166833 / 500000000000)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-6537945833 / 12500000000), (-261523386649 / 500000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-2602376682827 / 1000000000000), (-197989167833 / 100000000000), (-2602399216291 / 1000000000000), (0 / 1), (0 / 1)], ![(0 / 1), (-945044619211 / 500000000000), (170857518541 / 125000000000), (136684835883 / 100000000000), (-378018866733 / 200000000000)]]

private def alphaScale (c : MME.ReleasedInterior.Split 11) : ℤ :=
  ([3, 8, 2, 2, 8, 3] : List ℤ).getD
    ((seed 4 11).splits.idxOf (sourceShape 4 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 11) : ℚ :=
  ([(-1758575097297 / 1000000000000), (-5015506683119 / 1000000000000), (-11360783033 / 10000000000), (-1136078986143 / 1000000000000), (-125388380701 / 25000000000), (-1758574734607 / 1000000000000)] : List ℚ).getD
    ((seed 4 11).splits.idxOf (sourceShape 4 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 11) : ℚ :=
  ([(-109910943581 / 62500000000), (-2507753341559 / 500000000000), (-1136078303299 / 1000000000000), (-568039493071 / 500000000000), (-5015535228039 / 1000000000000), (-879287367303 / 500000000000)] : List ℚ).getD
    ((seed 4 11).splits.idxOf (sourceShape 4 c)) 0

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
        (splitWeight 4 11 0 c : ℝ) / 1000000000000) ≤
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
