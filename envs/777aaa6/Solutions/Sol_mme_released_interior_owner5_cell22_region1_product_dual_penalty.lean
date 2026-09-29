-- Prove2me | solution 1 for mme_released_interior_owner5_cell22_region1_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-24T17:22:05.36879+00:00
-- url     : https://prove2.me/submissions/be13852b-7a95-491a-9dd4-38a56f112ed1

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 22) : ℚ :=
  (splitWeight 5 22 1 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(116455277603 / 200000000000), (1051777104321 / 1000000000000), (582278468981 / 1000000000000), (1 / 1), (1 / 1)], ![(1 / 1), (155072192487 / 1000000000000), (962665649263 / 250000000000), (30805360009 / 8000000000), (19383971811 / 125000000000)], ![(74645057508750000000000000000000000 / 952844129926394512957941206086333069), (74645201791625000000000000000000000 / 952844129926394512957941206086333069), (1 / 1), (1 / 1), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![1, 0, 1, 0, 0], ![0, 3, -1, -1, 3], ![4, 4, 0, 0, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-540810050481 / 1000000000000), (12620303461 / 250000000000), (-540806476641 / 1000000000000), (0 / 1), (0 / 1)], ![(0 / 1), (-931932256257 / 500000000000), (674122618311 / 500000000000), (53929886377 / 40000000000), (-186386720803 / 100000000000)], ![(-2546707020077 / 1000000000000), (-63667627179 / 25000000000), (0 / 1), (0 / 1), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-6760125631 / 12500000000), (10096242769 / 200000000000), (-3380040479 / 6250000000), (0 / 1), (0 / 1)], ![(0 / 1), (-1863864512513 / 1000000000000), (1348245236623 / 1000000000000), (674123579713 / 500000000000), (-1863867208029 / 1000000000000)], ![(-636676755019 / 250000000000), (-2546705087159 / 1000000000000), (0 / 1), (0 / 1), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 22) : ℤ :=
  ([3, 2, 8, 8, 2, 3] : List ℤ).getD
    ((seed 5 22).splits.idxOf (sourceShape 5 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 22) : ℚ :=
  ([(-1739268260097 / 1000000000000), (-143497330851 / 125000000000), (-2475692139317 / 500000000000), (-99027521527 / 20000000000), (-114797863669 / 100000000000), (-1739267978217 / 1000000000000)] : List ℚ).getD
    ((seed 5 22).splits.idxOf (sourceShape 5 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 22) : ℚ :=
  ([(-6794016641 / 3906250000), (-1147978646807 / 1000000000000), (-4951384278633 / 1000000000000), (-4951376076349 / 1000000000000), (-1147978636689 / 1000000000000), (-217408497277 / 125000000000)] : List ℚ).getD
    ((seed 5 22).splits.idxOf (sourceShape 5 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 22) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 22 =>
        (splitWeight 5 22 1 c : ℝ) / 1000000000000) ≤
          (1 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 22, ∏ i, weights i (c.val i) ≤ 1 := by
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
