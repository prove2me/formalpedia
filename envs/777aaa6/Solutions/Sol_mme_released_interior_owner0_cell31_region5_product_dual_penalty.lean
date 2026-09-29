-- Prove2me | solution 1 for mme_released_interior_owner0_cell31_region5_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T12:44:03.772171+00:00
-- url     : https://prove2.me/submissions/08c422c0-3c86-4f4e-a2ec-841914fceead

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 31) : ℚ :=
  (splitWeight 0 31 5 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(5339799260600000000000000000000000 / 1746588129950642172201377742110975423), (206537627188700000000000000000000000 / 1746588129950642172201377742110975423), (1277179509129300000000000000000000000 / 1746588129950642172201377742110975423), (2005229357000000000000000000000000 / 16957166310200409438848327593310441), (5339799034400000000000000000000000 / 1746588129950642172201377742110975423)], ![(78906844763 / 200000000000), (15781413349 / 40000000000), (1 / 1), (1 / 1), (1 / 1)], ![(271533135049 / 1000000000000), (1453068208301 / 1000000000000), (1453072532757 / 1000000000000), (54306664857 / 200000000000), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![9, 4, 1, 4, 9], ![2, 2, 0, 0, 0], ![2, 0, 0, 2, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-23160925853 / 4000000000), (-2134936914077 / 1000000000000), (-39126263343 / 125000000000), (-2134932088903 / 1000000000000), (-5790231505611 / 1000000000000)], ![(-930049390077 / 1000000000000), (-186009315373 / 200000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-325917775669 / 250000000000), (37367732657 / 100000000000), (373680302651 / 1000000000000), (-2036985009 / 1562500000), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-5790231463249 / 1000000000000), (-533734228519 / 250000000000), (-313010106743 / 1000000000000), (-1067466044451 / 500000000000), (-579023150561 / 100000000000)], ![(-232512347519 / 250000000000), (-29063955527 / 31250000000), (0 / 1), (0 / 1), (0 / 1)], ![(-52146844107 / 40000000000), (373677326571 / 1000000000000), (93420075663 / 250000000000), (-1303670405759 / 1000000000000), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 31) : ℤ :=
  ([12, 7, 4, 2, 2, 4, 7, 12] : List ℤ).getD
    ((seed 0 31).splits.idxOf (sourceShape 0 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 31) : ℚ :=
  ([(-8023948444563 / 1000000000000), (-4368656709857 / 1000000000000), (-2691303188283 / 1000000000000), (-217344798543 / 250000000000), (-869379357037 / 1000000000000), (-2691304152417 / 1000000000000), (-4368649768431 / 1000000000000), (-1604790399701 / 200000000000)] : List ℚ).getD
    ((seed 0 31).splits.idxOf (sourceShape 0 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 31) : ℚ :=
  ([(-4011974222281 / 500000000000), (-136520522183 / 31250000000), (-1345651594141 / 500000000000), (-869379194171 / 1000000000000), (-217344839259 / 250000000000), (-84103254763 / 31250000000), (-436864976843 / 100000000000), (-1002993999813 / 125000000000)] : List ℚ).getD
    ((seed 0 31).splits.idxOf (sourceShape 0 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 31) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 31 =>
        (splitWeight 0 31 5 c : ℝ) / 1000000000000) ≤
          (1 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 31, ∏ i, weights i (c.val i) ≤ 1 := by
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
