-- Prove2me | solution 1 for mme_released_interior_owner2_cell11_region0_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T15:15:53.269966+00:00
-- url     : https://prove2.me/submissions/aed61ea4-6477-4f08-8e9a-034c469d9560

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 11) : ℚ :=
  (splitWeight 2 11 0 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(296210328049 / 500000000000), (592419678593 / 1000000000000), (1 / 1), (1 / 1), (1 / 1)], ![(114702896846600000000000000000000000 / 1549090432376627106606553908334757637), (213413691031000000000000000000000000 / 1549090432376627106606553908334757637), (114702492239800000000000000000000000 / 1549090432376627106606553908334757637), (1 / 1), (1 / 1)], ![(1 / 1), (150631539189 / 1000000000000), (196599290753 / 50000000000), (1965988220191 / 500000000000), (37658719889 / 250000000000)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![1, 1, 0, 0, 0], ![4, 3, 4, 0, 0], ![0, 3, -1, -1, 3]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-523538328699 / 1000000000000), (-523539978719 / 1000000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-162692371261 / 62500000000), (-1982190726379 / 1000000000000), (-520616293523 / 200000000000), (0 / 1), (0 / 1)], ![(0 / 1), (-1892918561977 / 1000000000000), (684572297357 / 500000000000), (684571105251 / 500000000000), (-75715855459 / 40000000000)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-261769164349 / 500000000000), (-261769989359 / 500000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-104123117607 / 40000000000), (-991095363189 / 500000000000), (-1301540733807 / 500000000000), (0 / 1), (0 / 1)], ![(0 / 1), (-236614820247 / 125000000000), (273828918943 / 200000000000), (1369142210503 / 1000000000000), (-946448193237 / 500000000000)]]

private def alphaScale (c : MME.ReleasedInterior.Split 11) : ℤ :=
  ([8, 3, 2, 2, 3, 8] : List ℤ).getD
    ((seed 2 11).splits.idxOf (sourceShape 2 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 11) : ℚ :=
  ([(-5019512655427 / 1000000000000), (-175747570839 / 100000000000), (-1136586844577 / 1000000000000), (-1136586110377 / 1000000000000), (-1098422001 / 625000000), (-1003908001679 / 200000000000)] : List ℚ).getD
    ((seed 2 11).splits.idxOf (sourceShape 2 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 11) : ℚ :=
  ([(-2509756327713 / 500000000000), (-1757475708389 / 1000000000000), (-35518338893 / 31250000000), (-142073263797 / 125000000000), (-1757475201599 / 1000000000000), (-2509770004197 / 500000000000)] : List ℚ).getD
    ((seed 2 11).splits.idxOf (sourceShape 2 c)) 0

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
        (splitWeight 2 11 0 c : ℝ) / 1000000000000) ≤
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
