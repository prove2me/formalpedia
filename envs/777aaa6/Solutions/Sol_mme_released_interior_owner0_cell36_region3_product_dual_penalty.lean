-- Prove2me | solution 1 for mme_released_interior_owner0_cell36_region3_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T12:44:12.566343+00:00
-- url     : https://prove2.me/submissions/07044c0b-d50b-41b3-b2db-da511f1d7b1b

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 36) : ℚ :=
  (splitWeight 0 36 3 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(1 / 1), (9870026920062500000000000000000000 / 471683093701955935349508725146321407), (237516515499687500000000000000000000 / 471683093701955935349508725146321407), (237516528104687500000000000000000000 / 471683093701955935349508725146321407), (3290006802562500000000000000000000 / 157227697900651978449836241715440469)], ![(599571324637 / 1000000000000), (599571339453 / 1000000000000), (1 / 1), (1 / 1), (1 / 1)], ![(587248380727 / 1000000000000), (1044444720837 / 1000000000000), (58724876043 / 100000000000), (1 / 1), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![0, 6, 1, 1, 6], ![1, 1, 0, 0, 0], ![1, 0, 1, 0, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(0 / 1), (-773360953507 / 200000000000), (-686070188437 / 1000000000000), (-686070135367 / 1000000000000), (-966701356837 / 250000000000)], ![(-127885084513 / 250000000000), (-511540313341 / 1000000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-53230741283 / 100000000000), (4348537657 / 100000000000), (-425845413 / 800000000), (0 / 1), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(0 / 1), (-1933402383767 / 500000000000), (-171517547109 / 250000000000), (-343035067683 / 500000000000), (-3866805427347 / 1000000000000)], ![(-511540338051 / 1000000000000), (-25577015667 / 50000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-532307412829 / 1000000000000), (43485376571 / 1000000000000), (-532306766249 / 1000000000000), (0 / 1), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 36) : ℤ :=
  ([8, 3, 2, 2, 3, 8] : List ℤ).getD
    ((seed 0 36).splits.idxOf (sourceShape 0 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 36) : ℚ :=
  ([(-2455325923563 / 500000000000), (-1729917292741 / 1000000000000), (-577062562603 / 500000000000), (-72132818553 / 62500000000), (-1729917861537 / 1000000000000), (-491065317821 / 100000000000)] : List ℚ).getD
    ((seed 0 36).splits.idxOf (sourceShape 0 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 36) : ℚ :=
  ([(-39285214777 / 8000000000), (-86495864637 / 50000000000), (-230825025041 / 200000000000), (-1154125096847 / 1000000000000), (-54059933173 / 31250000000), (-4910653178209 / 1000000000000)] : List ℚ).getD
    ((seed 0 36).splits.idxOf (sourceShape 0 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 36) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 36 =>
        (splitWeight 0 36 3 c : ℝ) / 1000000000000) ≤
          (1 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 36, ∏ i, weights i (c.val i) ≤ 1 := by
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
