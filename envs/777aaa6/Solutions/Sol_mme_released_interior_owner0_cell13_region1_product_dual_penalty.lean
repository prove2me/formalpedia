-- Prove2me | solution 1 for mme_released_interior_owner0_cell13_region1_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T12:25:10.507379+00:00
-- url     : https://prove2.me/submissions/fcedd928-6cf0-40ad-8ea2-06d584df8474

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 13) : ℚ :=
  (splitWeight 0 13 1 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(49160756251750000000000000000000000 / 2196904848162166288872109905340870547), (49159394232250000000000000000000000 / 2196904848162166288872109905340870547), (1 / 1), (1 / 1), (1 / 1)], ![(53306172051 / 1000000000000), (2034104968007 / 1000000000000), (6579890070173 / 500000000000), (2033983720601 / 1000000000000), (53306035879 / 1000000000000)], ![(13723807689 / 50000000000), (716468765699 / 500000000000), (28657974387 / 20000000000), (1715274607 / 6250000000), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![6, 6, 0, 0, 0], ![5, -1, -3, -1, 5], ![2, 0, 0, 2, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-474963636687 / 125000000000), (-1899868399651 / 500000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-586340631237 / 200000000000), (88756987873 / 125000000000), (322145652387 / 125000000000), (177499073489 / 250000000000), (-1465852855357 / 500000000000)], ![(-646445446641 / 500000000000), (89931638753 / 250000000000), (359699468993 / 1000000000000), (-1293008275249 / 1000000000000), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-759941818699 / 200000000000), (-3799736799301 / 1000000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-366462894523 / 125000000000), (142011180597 / 200000000000), (2577165219097 / 1000000000000), (709996293957 / 1000000000000), (-2931705710713 / 1000000000000)], ![(-1292890893281 / 1000000000000), (359726555013 / 1000000000000), (179849734497 / 500000000000), (-80813017203 / 62500000000), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 13) : ℤ :=
  ([7, 2, 4, 12, 12, 4, 2, 7] : List ℤ).getD
    ((seed 0 13).splits.idxOf (sourceShape 0 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 13) : ℚ :=
  ([(-4382661465737 / 1000000000000), (-26963887669 / 31250000000), (-2729986244519 / 1000000000000), (-250759553037 / 31250000000), (-401222411507 / 50000000000), (-1364990713663 / 500000000000), (-107855628149 / 125000000000), (-4382631398627 / 1000000000000)] : List ℚ).getD
    ((seed 0 13).splits.idxOf (sourceShape 0 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 13) : ℚ :=
  ([(-547832683217 / 125000000000), (-862844405407 / 1000000000000), (-1364993122259 / 500000000000), (-8024305697183 / 1000000000000), (-8024448230139 / 1000000000000), (-109199257093 / 40000000000), (-862845025191 / 1000000000000), (-2191315699313 / 500000000000)] : List ℚ).getD
    ((seed 0 13).splits.idxOf (sourceShape 0 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 13) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 13 =>
        (splitWeight 0 13 1 c : ℝ) / 1000000000000) ≤
          (1 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 13, ∏ i, weights i (c.val i) ≤ 1 := by
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
