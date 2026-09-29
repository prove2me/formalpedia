-- Prove2me | solution 1 for mme_released_interior_owner4_cell18_region1_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-24T17:16:13.13382+00:00
-- url     : https://prove2.me/submissions/9f9e55e2-a522-4c58-90e9-0f986f3a17bb

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 18) : ℚ :=
  (splitWeight 4 18 1 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(574067255079 / 1000000000000), (1064598135113 / 1000000000000), (574065665293 / 1000000000000), (1 / 1), (1 / 1)], ![(74039683389500000000000000000000000 / 968521163512819213541115767809618759), (74039581154375000000000000000000000 / 968521163512819213541115767809618759), (1 / 1), (1 / 1), (1 / 1)], ![(1 / 1), (293632551 / 1953125000), (492341338159 / 125000000000), (984681276637 / 250000000000), (150339641883 / 1000000000000)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![1, 0, 1, 0, 0], ![4, 4, 0, 0, 0], ![0, 3, -1, -1, 3]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-1387521801 / 2500000000), (62597390029 / 1000000000000), (-555011489741 / 1000000000000), (0 / 1), (0 / 1)], ![(-2571169122967 / 1000000000000), (-321396312973 / 125000000000), (0 / 1), (0 / 1), (0 / 1)], ![(0 / 1), (-947428386901 / 500000000000), (171357314423 / 125000000000), (1370857093929 / 1000000000000), (-473714566321 / 250000000000)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-555008720399 / 1000000000000), (6259739003 / 100000000000), (-27750574487 / 50000000000), (0 / 1), (0 / 1)], ![(-1285584561483 / 500000000000), (-2571170503783 / 1000000000000), (0 / 1), (0 / 1), (0 / 1)], ![(0 / 1), (-1894856773801 / 1000000000000), (274171703077 / 200000000000), (137085709393 / 100000000000), (-1894858265283 / 1000000000000)]]

private def alphaScale (c : MME.ReleasedInterior.Split 18) : ℤ :=
  ([3, 2, 8, 8, 2, 3] : List ℤ).getD
    ((seed 4 18).splits.idxOf (sourceShape 4 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 18) : ℚ :=
  ([(-438830524331 / 250000000000), (-1137714639009 / 1000000000000), (-5021036108633 / 1000000000000), (-78453730739 / 15625000000), (-113771459837 / 100000000000), (-877661065127 / 500000000000)] : List ℚ).getD
    ((seed 4 18).splits.idxOf (sourceShape 4 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 18) : ℚ :=
  ([(-1755322097323 / 1000000000000), (-35553582469 / 31250000000), (-627629513579 / 125000000000), (-1004207753459 / 200000000000), (-1137714598369 / 1000000000000), (-1755322130253 / 1000000000000)] : List ℚ).getD
    ((seed 4 18).splits.idxOf (sourceShape 4 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 18) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 18 =>
        (splitWeight 4 18 1 c : ℝ) / 1000000000000) ≤
          (1 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 18, ∏ i, weights i (c.val i) ≤ 1 := by
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
