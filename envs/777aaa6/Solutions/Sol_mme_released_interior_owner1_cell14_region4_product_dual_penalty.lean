-- Prove2me | solution 1 for mme_released_interior_owner1_cell14_region4_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T13:17:14.03309+00:00
-- url     : https://prove2.me/submissions/9a14c942-97b9-4292-a644-7ab39d1f87ad

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 14) : ℚ :=
  (splitWeight 1 14 4 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(298982987743000000000000000000000000 / 3801211328412778304294946954621249813), (298980810413000000000000000000000000 / 3801211328412778304294946954621249813), (1 / 1), (1 / 1), (1 / 1)], ![(1 / 1), (38991297461 / 250000000000), (1916979677463 / 500000000000), (1916965686661 / 500000000000), (155965046981 / 1000000000000)], ![(583222115377 / 1000000000000), (42044815099 / 40000000000), (58321378927 / 100000000000), (1 / 1), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![4, 4, 0, 0, 0], ![0, 3, -1, -1, 3], ![1, 0, 1, 0, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-1271344195481 / 500000000000), (-2542695673443 / 1000000000000), (0 / 1), (0 / 1), (0 / 1)], ![(0 / 1), (-1858122438659 / 1000000000000), (335974510837 / 250000000000), (335972686241 / 250000000000), (-464530838663 / 250000000000)], ![(-107837435653 / 200000000000), (12464155367 / 250000000000), (-107840290883 / 200000000000), (0 / 1), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-2542688390961 / 1000000000000), (-1271347836721 / 500000000000), (0 / 1), (0 / 1), (0 / 1)], ![(0 / 1), (-929061219329 / 500000000000), (1343898043349 / 1000000000000), (268778148993 / 200000000000), (-1858123354651 / 1000000000000)], ![(-67398397283 / 125000000000), (49856621469 / 1000000000000), (-269600727207 / 500000000000), (0 / 1), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 14) : ℤ :=
  ([8, 2, 3, 3, 2, 8] : List ℤ).getD
    ((seed 1 14).splits.idxOf (sourceShape 1 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 14) : ℚ :=
  ([(-2469999461977 / 500000000000), (-71808814033 / 62500000000), (-1737991802029 / 1000000000000), (-1737992106743 / 1000000000000), (-9191528069 / 8000000000), (-4940019566533 / 1000000000000)] : List ℚ).getD
    ((seed 1 14).splits.idxOf (sourceShape 1 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 14) : ℚ :=
  ([(-4939998923953 / 1000000000000), (-1148941024527 / 1000000000000), (-434497950507 / 250000000000), (-868996053371 / 500000000000), (-71808813039 / 62500000000), (-1235004891633 / 250000000000)] : List ℚ).getD
    ((seed 1 14).splits.idxOf (sourceShape 1 c)) 0

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
        (splitWeight 1 14 4 c : ℝ) / 1000000000000) ≤
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
