-- Prove2me | solution 1 for mme_released_interior_owner1_cell10_region5_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T12:44:27.613765+00:00
-- url     : https://prove2.me/submissions/81e2810f-e97f-4351-a52f-4de59a30e889

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 10) : ℚ :=
  (splitWeight 1 10 5 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(848135221408000000000000000000000000 / 3776568569155354813652363710367464849), (848553603115000000000000000000000000 / 3776568569155354813652363710367464849), (1 / 1), (1 / 1), (1 / 1)], ![(850506579523 / 1000000000000), (425378685261 / 500000000000), (1 / 1), (1 / 1), (1 / 1)], ![(1 / 1), (1 / 1), (298783280547 / 500000000000), (2016698229149 / 1000000000000), (481946737 / 800000000)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![3, 3, 0, 0, 0], ![1, 1, 0, 0, 0], ![0, 0, 1, -1, 1]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-746765504051 / 500000000000), (-1493037833739 / 1000000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-20240391389 / 125000000000), (-161628302081 / 1000000000000), (0 / 1), (0 / 1), (0 / 1)], ![(0 / 1), (0 / 1), (-514889602061 / 1000000000000), (701461634069 / 1000000000000), (-506778123873 / 1000000000000)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-1493531008101 / 1000000000000), (-746518916869 / 500000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-161923131111 / 1000000000000), (-126272111 / 781250000), (0 / 1), (0 / 1), (0 / 1)], ![(0 / 1), (0 / 1), (-25744480103 / 50000000000), (70146163407 / 100000000000), (-15836816371 / 31250000000)]]

private def alphaScale (c : MME.ReleasedInterior.Split 10) : ℤ :=
  ([2, 4, 4, 2] : List ℤ).getD
    ((seed 1 10).splits.idxOf (sourceShape 1 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 10) : ℚ :=
  ([(-59606104757 / 62500000000), (-2162232263089 / 1000000000000), (-1084777868941 / 500000000000), (-47674966539 / 50000000000)] : List ℚ).getD
    ((seed 1 10).splits.idxOf (sourceShape 1 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 10) : ℚ :=
  ([(-953697676111 / 1000000000000), (-135139516443 / 62500000000), (-2169555737881 / 1000000000000), (-953499330779 / 1000000000000)] : List ℚ).getD
    ((seed 1 10).splits.idxOf (sourceShape 1 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 10) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 10 =>
        (splitWeight 1 10 5 c : ℝ) / 1000000000000) ≤
          (1 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 10, ∏ i, weights i (c.val i) ≤ 1 := by
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
