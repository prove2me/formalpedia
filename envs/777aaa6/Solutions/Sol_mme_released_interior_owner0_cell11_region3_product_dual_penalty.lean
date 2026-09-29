-- Prove2me | solution 1 for mme_released_interior_owner0_cell11_region3_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T12:25:06.975852+00:00
-- url     : https://prove2.me/submissions/3c891b7d-5be4-4894-ab8d-cb1105d7de28

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 11) : ℚ :=
  (splitWeight 0 11 3 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(11853807053340000000000000000000000 / 154767843138650082043616788142081909), (11853793910780000000000000000000000 / 154767843138650082043616788142081909), (1 / 1), (1 / 1), (1 / 1)], ![(114675399373 / 200000000000), (26714400627 / 25000000000), (3583598629 / 6250000000), (1 / 1), (1 / 1)], ![(1 / 1), (151053137247 / 1000000000000), (3923127386779 / 1000000000000), (3923122805393 / 1000000000000), (151053211189 / 1000000000000)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![4, 4, 0, 0, 0], ![1, 0, 1, 0, 0], ![0, 3, -1, -1, 3]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-1284638560803 / 500000000000), (-2569278230327 / 1000000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-27810592171 / 50000000000), (66326944467 / 1000000000000), (-69526745573 / 125000000000), (0 / 1), (0 / 1)], ![(0 / 1), (-1890123601773 / 1000000000000), (341722284619 / 250000000000), (683443985343 / 500000000000), (-1890123112263 / 1000000000000)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-513855424321 / 200000000000), (-1284639115163 / 500000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-556211843419 / 1000000000000), (16581736117 / 250000000000), (-556213964583 / 1000000000000), (0 / 1), (0 / 1)], ![(0 / 1), (-472530900443 / 250000000000), (1366889138477 / 1000000000000), (1366887970687 / 1000000000000), (-945061556131 / 500000000000)]]

private def alphaScale (c : MME.ReleasedInterior.Split 11) : ℤ :=
  ([8, 2, 3, 3, 2, 8] : List ℤ).getD
    ((seed 0 11).splits.idxOf (sourceShape 0 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 11) : ℚ :=
  ([(-1253903019341 / 250000000000), (-1136062206451 / 1000000000000), (-1758601947713 / 1000000000000), (-87930105153 / 50000000000), (-1136062147379 / 1000000000000), (-1003123159357 / 200000000000)] : List ℚ).getD
    ((seed 0 11).splits.idxOf (sourceShape 0 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 11) : ℚ :=
  ([(-5015612077363 / 1000000000000), (-22721244129 / 20000000000), (-27478155433 / 15625000000), (-1758602103059 / 1000000000000), (-568031073689 / 500000000000), (-313475987299 / 62500000000)] : List ℚ).getD
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
        (splitWeight 0 11 3 c : ℝ) / 1000000000000) ≤
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
