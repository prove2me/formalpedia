-- Prove2me | solution 1 for mme_released_interior_owner0_cell14_region1_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T12:25:13.598467+00:00
-- url     : https://prove2.me/submissions/f14cd1eb-6ae9-4981-a06c-500f96ac6695

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 14) : ℚ :=
  (splitWeight 0 14 1 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(597210201333000000000000000000000000 / 7621493822976097024065431995172506691), (597210500426000000000000000000000000 / 7621493822976097024065431995172506691), (1 / 1), (1 / 1), (1 / 1)], ![(1 / 1), (38775439363 / 250000000000), (3850245402693 / 1000000000000), (1925123774281 / 500000000000), (155101647379 / 1000000000000)], ![(582436628071 / 1000000000000), (525686996649 / 500000000000), (58243755887 / 100000000000), (1 / 1), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![4, 4, 0, 0, 0], ![0, 3, -1, -1, 3], ![1, 0, 1, 0, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-636614630443 / 250000000000), (-509291604191 / 200000000000), (0 / 1), (0 / 1), (0 / 1)], ![(0 / 1), (-74546955111 / 40000000000), (1348136887227 / 1000000000000), (16851718057 / 12500000000), (-1863674587457 / 1000000000000)], ![(-67566861559 / 125000000000), (5009787379 / 100000000000), (-270266647181 / 500000000000), (0 / 1), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-2546458521771 / 1000000000000), (-1273229010477 / 500000000000), (0 / 1), (0 / 1), (0 / 1)], ![(0 / 1), (-931836938887 / 500000000000), (337034221807 / 250000000000), (1348137444561 / 1000000000000), (-29119915429 / 15625000000)], ![(-540534892471 / 1000000000000), (50097873791 / 1000000000000), (-540533294361 / 1000000000000), (0 / 1), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 14) : ℤ :=
  ([3, 2, 8, 8, 2, 3] : List ℤ).getD
    ((seed 0 14).splits.idxOf (sourceShape 0 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 14) : ℚ :=
  ([(-434713732227 / 250000000000), (-1148223203421 / 1000000000000), (-2475334000843 / 500000000000), (-990133038623 / 200000000000), (-574111629969 / 500000000000), (-27169616701 / 15625000000)] : List ℚ).getD
    ((seed 0 14).splits.idxOf (sourceShape 0 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 14) : ℚ :=
  ([(-1738854928907 / 1000000000000), (-57411160171 / 50000000000), (-990133600337 / 200000000000), (-2475332596557 / 500000000000), (-1148223259937 / 1000000000000), (-1738855468863 / 1000000000000)] : List ℚ).getD
    ((seed 0 14).splits.idxOf (sourceShape 0 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 14) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 14 =>
        (splitWeight 0 14 1 c : ℝ) / 1000000000000) ≤
          (1 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 14, ∏ i, weights i (c.val i) ≤ 1 := by
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
