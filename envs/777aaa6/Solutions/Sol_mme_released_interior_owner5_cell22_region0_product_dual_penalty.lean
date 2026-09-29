-- Prove2me | solution 1 for mme_released_interior_owner5_cell22_region0_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-24T09:22:48.002636+00:00
-- url     : https://prove2.me/submissions/40c68ff4-b357-4ee9-b883-64571fababea

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 22) : ℚ :=
  (splitWeight 5 22 0 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(23328756589 / 40000000000), (65707219583 / 62500000000), (291606002637 / 500000000000), (1 / 1), (1 / 1)], ![(1 / 1), (39008635069 / 250000000000), (3832456915673 / 1000000000000), (3832430755091 / 1000000000000), (156034127839 / 1000000000000)], ![(598017578444000000000000000000000000 / 7601080369418048436539415024252941689), (598014146923000000000000000000000000 / 7601080369418048436539415024252941689), (1 / 1), (1 / 1), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![1, 0, 1, 0, 0], ![0, 3, -1, -1, 3], ![4, 4, 0, 0, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-269596333079 / 500000000000), (50042249819 / 1000000000000), (-21568180533 / 40000000000), (0 / 1), (0 / 1)], ![(0 / 1), (-371535576843 / 200000000000), (1343506089867 / 1000000000000), (1343499263783 / 1000000000000), (-1857680527461 / 1000000000000)], ![(-2542425521133 / 1000000000000), (-254243125931 / 100000000000), (0 / 1), (0 / 1), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-539192666157 / 1000000000000), (2502112491 / 50000000000), (-134801128331 / 250000000000), (0 / 1), (0 / 1)], ![(0 / 1), (-928838942107 / 500000000000), (335876522467 / 250000000000), (167937407973 / 125000000000), (-92884026373 / 50000000000)], ![(-635606380283 / 250000000000), (-2542431259309 / 1000000000000), (0 / 1), (0 / 1), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 22) : ℤ :=
  ([3, 2, 8, 8, 2, 3] : List ℤ).getD
    ((seed 5 22).splits.idxOf (sourceShape 5 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 22) : ℚ :=
  ([(-1738123944589 / 1000000000000), (-114888400753 / 100000000000), (-12348246787 / 2500000000), (-4939313656911 / 1000000000000), (-1148882919623 / 1000000000000), (-434531165421 / 250000000000)] : List ℚ).getD
    ((seed 5 22).splits.idxOf (sourceShape 5 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 22) : ℚ :=
  ([(-434530986147 / 250000000000), (-1148884007529 / 1000000000000), (-4939298714799 / 1000000000000), (-493931365691 / 100000000000), (-574441459811 / 500000000000), (-1738124661683 / 1000000000000)] : List ℚ).getD
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
        (splitWeight 5 22 0 c : ℝ) / 1000000000000) ≤
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
