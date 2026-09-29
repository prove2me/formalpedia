-- Prove2me | solution 1 for mme_released_interior_owner2_cell18_region0_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T15:35:27.801177+00:00
-- url     : https://prove2.me/submissions/dcf0cd2d-c262-4065-9597-a8af55dfe327

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 18) : ℚ :=
  (splitWeight 2 18 0 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(17939022111 / 31250000000), (266122165403 / 250000000000), (35877711553 / 62500000000), (1 / 1), (1 / 1)], ![(37017078403750000000000000000000000 / 484336043034842919020195831974875251), (37016908769000000000000000000000000 / 484336043034842919020195831974875251), (1 / 1), (1 / 1), (1 / 1)], ![(1 / 1), (75139944351 / 500000000000), (984999818611 / 250000000000), (787995937779 / 200000000000), (150279496717 / 1000000000000)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![1, 0, 1, 0, 0], ![4, 4, 0, 0, 0], ![0, 3, -1, -1, 3]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-555041029901 / 1000000000000), (195295481 / 3125000000), (-6938128777 / 12500000000), (0 / 1), (0 / 1)], ![(-2571399584961 / 1000000000000), (-128570208379 / 50000000000), (0 / 1), (0 / 1), (0 / 1)], ![(0 / 1), (-1895255798881 / 1000000000000), (685590269579 / 500000000000), (1371175568193 / 1000000000000), (-1895258407251 / 1000000000000)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-5550410299 / 10000000000), (62494553921 / 1000000000000), (-555050302159 / 1000000000000), (0 / 1), (0 / 1)], ![(-8035623703 / 3125000000), (-2571404167579 / 1000000000000), (0 / 1), (0 / 1), (0 / 1)], ![(0 / 1), (-11845348743 / 6250000000), (1371180539159 / 1000000000000), (685587784097 / 500000000000), (-7581033629 / 4000000000)]]

private def alphaScale (c : MME.ReleasedInterior.Split 18) : ℤ :=
  ([8, 2, 3, 3, 2, 8] : List ℤ).getD
    ((seed 2 18).splits.idxOf (sourceShape 2 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 18) : ℚ :=
  ([(-5021699022047 / 1000000000000), (-1137729462849 / 1000000000000), (-877634673981 / 500000000000), (-1755269629287 / 1000000000000), (-2275458149 / 2000000000), (-5021710268653 / 1000000000000)] : List ℚ).getD
    ((seed 2 18).splits.idxOf (sourceShape 2 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 18) : ℚ :=
  ([(-1004339804409 / 200000000000), (-17777022857 / 15625000000), (-1755269347961 / 1000000000000), (-877634814643 / 500000000000), (-1137729074499 / 1000000000000), (-1255427567163 / 250000000000)] : List ℚ).getD
    ((seed 2 18).splits.idxOf (sourceShape 2 c)) 0

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
        (splitWeight 2 18 0 c : ℝ) / 1000000000000) ≤
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
