-- Prove2me | solution 1 for mme_released_interior_owner0_cell25_region0_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T12:37:25.431506+00:00
-- url     : https://prove2.me/submissions/57f5fafd-e487-4654-b73e-124cb8d03bde

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 25) : ℚ :=
  (splitWeight 0 25 0 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(55503314736400000000000000000000000 / 3555982345100306213068988865311071069), (281803520221600000000000000000000000 / 3555982345100306213068988865311071069), (281804168259800000000000000000000000 / 3555982345100306213068988865311071069), (55503441629800000000000000000000000 / 3555982345100306213068988865311071069), (1 / 1)], ![(391053025981 / 1000000000000), (391053892801 / 1000000000000), (1 / 1), (1 / 1), (1 / 1)], ![(13313305921 / 250000000000), (1985117543977 / 1000000000000), (13747572724211 / 1000000000000), (79405009493 / 40000000000), (53253222113 / 1000000000000)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![7, 4, 4, 7, 0], ![2, 2, 0, 0, 0], ![5, 0, -3, 0, 5]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-4159943887853 / 1000000000000), (-2535176540501 / 1000000000000), (-2535174240893 / 1000000000000), (-33279532813 / 8000000000), (0 / 1)], ![(-938912111873 / 1000000000000), (-187781979049 / 200000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-2932696937559 / 1000000000000), (137135625699 / 200000000000), (2620862279381 / 1000000000000), (171420501 / 250000000), (-2932696967059 / 1000000000000)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-1039985971963 / 250000000000), (-5070353081 / 2000000000), (-633793560223 / 250000000000), (-519992700203 / 125000000000), (0 / 1)], ![(-3667625437 / 3906250000), (-234727473811 / 250000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-1466348468779 / 500000000000), (42854883031 / 62500000000), (1310431139691 / 500000000000), (685682004001 / 1000000000000), (-1466348483529 / 500000000000)]]

private def alphaScale (c : MME.ReleasedInterior.Split 25) : ℤ :=
  ([12, 7, 5, 2, 2, 5, 7, 12] : List ℤ).getD
    ((seed 0 25).splits.idxOf (sourceShape 0 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 25) : ℚ :=
  ([(-401577648297 / 50000000000), (-4413171779133 / 1000000000000), (-2788406648369 / 1000000000000), (-213306039091 / 250000000000), (-426612036693 / 500000000000), (-1394203003821 / 500000000000), (-4413175584967 / 1000000000000), (-8031548434243 / 1000000000000)] : List ℚ).getD
    ((seed 0 25).splits.idxOf (sourceShape 0 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 25) : ℚ :=
  ([(-8031552965939 / 1000000000000), (-1103292944783 / 250000000000), (-174275415523 / 62500000000), (-853224156363 / 1000000000000), (-170644814677 / 200000000000), (-2788406007641 / 1000000000000), (-2206587792483 / 500000000000), (-4015774217121 / 500000000000)] : List ℚ).getD
    ((seed 0 25).splits.idxOf (sourceShape 0 c)) 0

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
        (splitWeight 0 25 0 c : ℝ) / 1000000000000) ≤
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
