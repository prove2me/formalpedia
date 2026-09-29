-- Prove2me | solution 1 for mme_released_interior_owner2_cell21_region2_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T15:39:16.226488+00:00
-- url     : https://prove2.me/submissions/b0620b1a-097e-479d-94b1-d35787901cfd

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 21) : ℚ :=
  (splitWeight 2 21 2 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(402495111959 / 1000000000000), (209980911059 / 250000000000), (402497617493 / 1000000000000), (1 / 1), (1 / 1)], ![(4871055145750000000000000000000000 / 2496901637589352450014552324532448143), (286499641736250000000000000000000000 / 2496901637589352450014552324532448143), (2138863862403375000000000000000000000 / 2496901637589352450014552324532448143), (286501444733875000000000000000000000 / 2496901637589352450014552324532448143), (4871055483375000000000000000000000 / 2496901637589352450014552324532448143)], ![(418689143103 / 1000000000000), (193978455421 / 250000000000), (20934587759 / 50000000000), (1 / 1), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![2, 1, 2, 0, 0], ![10, 4, 1, 4, 10], ![2, 1, 2, 0, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-910072326399 / 1000000000000), (-43611072749 / 250000000000), (-455033050707 / 500000000000), (0 / 1), (0 / 1)], ![(-6239495321271 / 1000000000000), (-5412671529 / 2500000000), (-154775835653 / 1000000000000), (-1082531159213 / 500000000000), (-6239495251959 / 1000000000000)], ![(-217656634077 / 250000000000), (-253713819497 / 1000000000000), (-6964962381 / 8000000000), (0 / 1), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-455036163199 / 500000000000), (-34888858199 / 200000000000), (-910066101413 / 1000000000000), (0 / 1), (0 / 1)], ![(-623949532127 / 100000000000), (-2165068611599 / 1000000000000), (-38693958913 / 250000000000), (-86602492737 / 40000000000), (-3119747625979 / 500000000000)], ![(-870626536307 / 1000000000000), (-31714227437 / 125000000000), (-108827537203 / 125000000000), (0 / 1), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 21) : ℤ :=
  ([12, 5, 5, 3, 1, 3, 5, 5, 12] : List ℤ).getD
    ((seed 2 21).splits.idxOf (sourceShape 2 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 21) : ℚ :=
  ([(-501261357513 / 62500000000), (-3210133165209 / 1000000000000), (-3328848571949 / 1000000000000), (-1935468469459 / 1000000000000), (-18216685817 / 31250000000), (-387093692717 / 200000000000), (-3328848424911 / 1000000000000), (-802533295187 / 250000000000), (-1604038823067 / 200000000000)] : List ℚ).getD
    ((seed 2 21).splits.idxOf (sourceShape 2 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 21) : ℚ :=
  ([(-8020181720207 / 1000000000000), (-401266645651 / 125000000000), (-832212142987 / 250000000000), (-967734234729 / 500000000000), (-582933946143 / 1000000000000), (-60483389487 / 31250000000), (-332884842491 / 100000000000), (-3210133180747 / 1000000000000), (-4010097057667 / 500000000000)] : List ℚ).getD
    ((seed 2 21).splits.idxOf (sourceShape 2 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 21) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 21 =>
        (splitWeight 2 21 2 c : ℝ) / 1000000000000) ≤
          (1 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 21, ∏ i, weights i (c.val i) ≤ 1 := by
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
