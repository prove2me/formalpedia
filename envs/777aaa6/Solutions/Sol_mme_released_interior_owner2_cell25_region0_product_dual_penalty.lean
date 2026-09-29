-- Prove2me | solution 1 for mme_released_interior_owner2_cell25_region0_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T15:39:22.306487+00:00
-- url     : https://prove2.me/submissions/4a383431-8973-41f3-9e3d-ea3c00b69c87

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 25) : ℚ :=
  (splitWeight 2 25 0 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(11181150207 / 40000000000), (350080264087 / 250000000000), (140031668243 / 100000000000), (279528102967 / 1000000000000), (1 / 1)], ![(97855757086000000000000000000000000 / 4435209863239278423071407152415501021), (97855463619000000000000000000000000 / 4435209863239278423071407152415501021), (1 / 1), (1 / 1), (1 / 1)], ![(5320032307 / 100000000000), (1986235343263 / 1000000000000), (551605130791 / 40000000000), (397244980643 / 200000000000), (13300081047 / 250000000000)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![2, 0, 0, 2, 0], ![6, 6, 0, 0, 0], ![5, 0, -3, 0, 5]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-127465011091 / 100000000000), (84175384073 / 250000000000), (336698412777 / 1000000000000), (-637326222077 / 500000000000), (0 / 1)], ![(-1906917842733 / 500000000000), (-1906919342223 / 500000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-2933690809909 / 1000000000000), (686241059741 / 1000000000000), (2623952993413 / 1000000000000), (686235803529 / 1000000000000), (-1466845394447 / 500000000000)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-1274650110909 / 1000000000000), (336701536293 / 1000000000000), (168349206389 / 500000000000), (-1274652444153 / 1000000000000), (0 / 1)], ![(-762767137093 / 200000000000), (-762767736889 / 200000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-733422702477 / 250000000000), (343120529871 / 500000000000), (1311976496707 / 500000000000), (68623580353 / 100000000000), (-2933690788893 / 1000000000000)]]

private def alphaScale (c : MME.ReleasedInterior.Split 25) : ℤ :=
  ([12, 5, 2, 7, 7, 2, 5, 12] : List ℤ).getD
    ((seed 2 25).splits.idxOf (sourceShape 2 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 25) : ℚ :=
  ([(-401108829161 / 50000000000), (-1395449172821 / 500000000000), (-426592139637 / 500000000000), (-275140441869 / 62500000000), (-4402252991823 / 1000000000000), (-853184154741 / 1000000000000), (-558179842387 / 200000000000), (-4011090969113 / 500000000000)] : List ℚ).getD
    ((seed 2 25).splits.idxOf (sourceShape 2 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 25) : ℚ :=
  ([(-8022176583219 / 1000000000000), (-2790898345641 / 1000000000000), (-853184279273 / 1000000000000), (-4402247069903 / 1000000000000), (-2201126495911 / 500000000000), (-42659207737 / 50000000000), (-1395449605967 / 500000000000), (-320887277529 / 40000000000)] : List ℚ).getD
    ((seed 2 25).splits.idxOf (sourceShape 2 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 25) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 25 =>
        (splitWeight 2 25 0 c : ℝ) / 1000000000000) ≤
          (1 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 25, ∏ i, weights i (c.val i) ≤ 1 := by
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
