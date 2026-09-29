-- Prove2me | solution 1 for mme_released_interior_owner0_cell15_region3_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T12:25:18.786034+00:00
-- url     : https://prove2.me/submissions/fce3af0f-7898-479f-b1cc-e20b98844602

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 15) : ℚ :=
  (splitWeight 0 15 3 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(424932852917500000000000000000000000 / 1872720524885385173884308888750289271), (425054893300500000000000000000000000 / 1872720524885385173884308888750289271), (1 / 1), (1 / 1), (1 / 1)], ![(1 / 1), (1 / 1), (302002064051 / 500000000000), (123816364829 / 62500000000), (606300087137 / 1000000000000)], ![(106479424511 / 125000000000), (34079727657 / 40000000000), (1 / 1), (1 / 1), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![3, 3, 0, 0, 0], ![0, 0, 1, 0, 1], ![1, 1, 0, 0, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-29664326309 / 20000000000), (-741464578733 / 500000000000), (0 / 1), (0 / 1), (0 / 1)], ![(0 / 1), (0 / 1), (-100834849293 / 200000000000), (136726596481 / 200000000000), (-250190111093 / 500000000000)], ![(-80180983949 / 500000000000), (-16017674347 / 100000000000), (0 / 1), (0 / 1), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-1483216315449 / 1000000000000), (-296585831493 / 200000000000), (0 / 1), (0 / 1), (0 / 1)], ![(0 / 1), (0 / 1), (-7877722601 / 15625000000), (341816491203 / 500000000000), (-100076044437 / 200000000000)], ![(-160361967897 / 1000000000000), (-160176743469 / 1000000000000), (0 / 1), (0 / 1), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 15) : ℤ :=
  ([2, 4, 4, 2] : List ℤ).getD
    ((seed 0 15).splits.idxOf (sourceShape 0 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 15) : ℚ :=
  ([(-191952015303 / 200000000000), (-2143958505529 / 1000000000000), (-2147280147403 / 1000000000000), (-479829071479 / 500000000000)] : List ℚ).getD
    ((seed 0 15).splits.idxOf (sourceShape 0 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 15) : ℚ :=
  ([(-479880038257 / 500000000000), (-267994813191 / 125000000000), (-1073640073701 / 500000000000), (-959658142957 / 1000000000000)] : List ℚ).getD
    ((seed 0 15).splits.idxOf (sourceShape 0 c)) 0

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
        (splitWeight 0 15 3 c : ℝ) / 1000000000000) ≤
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
