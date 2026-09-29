-- Prove2me | solution 1 for mme_released_interior_owner0_cell36_region4_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T12:44:13.417098+00:00
-- url     : https://prove2.me/submissions/603ba06b-68f2-4f22-aed5-2ab2f9a1f5af

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 36) : ℚ :=
  (splitWeight 0 36 4 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(1 / 1), (39272327462250000000000000000000000 / 1894336766455153061648851847620663919), (136170673302500000000000000000000000 / 270619538065021865949835978231523417), (953193597992500000000000000000000000 / 1894336766455153061648851847620663919), (39272273575000000000000000000000000 / 1894336766455153061648851847620663919)], ![(23957558369 / 40000000000), (598938261903 / 1000000000000), (1 / 1), (1 / 1), (1 / 1)], ![(584355710589 / 1000000000000), (105063434591 / 100000000000), (292177353269 / 500000000000), (1 / 1), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![0, 6, 1, 1, 6], ![1, 1, 0, 0, 0], ![1, 0, 1, 0, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(0 / 1), (-775220785981 / 200000000000), (-686804866187 / 1000000000000), (-686806036069 / 1000000000000), (-3876105302049 / 1000000000000)], ![(-256297795263 / 500000000000), (-128149188697 / 250000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-268622694051 / 500000000000), (6174265089 / 125000000000), (-537247106323 / 1000000000000), (0 / 1), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(0 / 1), (-242256495619 / 62500000000), (-343402433093 / 500000000000), (-171701509017 / 250000000000), (-121128290689 / 31250000000)], ![(-20503823621 / 40000000000), (-512596754787 / 1000000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-537245388101 / 1000000000000), (49394120713 / 1000000000000), (-268623553161 / 500000000000), (0 / 1), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 36) : ℤ :=
  ([8, 3, 2, 2, 3, 8] : List ℤ).getD
    ((seed 0 36).splits.idxOf (sourceShape 0 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 36) : ℚ :=
  ([(-4925947791037 / 1000000000000), (-1736647563039 / 1000000000000), (-57500375013 / 50000000000), (-575003752941 / 500000000000), (-434162044739 / 250000000000), (-492594628067 / 100000000000)] : List ℚ).getD
    ((seed 0 36).splits.idxOf (sourceShape 0 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 36) : ℚ :=
  ([(-1231486947759 / 250000000000), (-868323781519 / 500000000000), (-1150007500259 / 1000000000000), (-1150007505881 / 1000000000000), (-347329635791 / 200000000000), (-4925946280669 / 1000000000000)] : List ℚ).getD
    ((seed 0 36).splits.idxOf (sourceShape 0 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 36) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 36 =>
        (splitWeight 0 36 4 c : ℝ) / 1000000000000) ≤
          (1 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 36, ∏ i, weights i (c.val i) ≤ 1 := by
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
