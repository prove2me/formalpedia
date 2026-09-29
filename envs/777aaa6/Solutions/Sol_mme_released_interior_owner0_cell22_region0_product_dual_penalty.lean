-- Prove2me | solution 1 for mme_released_interior_owner0_cell22_region0_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T12:37:19.605197+00:00
-- url     : https://prove2.me/submissions/4baf2b5f-ed73-4d9c-a233-18fa3c4a22d6

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 22) : ℚ :=
  (splitWeight 0 22 0 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(290553069498500000000000000000000000 / 3815927055708423778977203438385635111), (527445282118500000000000000000000000 / 3815927055708423778977203438385635111), (290547525540000000000000000000000000 / 3815927055708423778977203438385635111), (1 / 1), (1 / 1)], ![(1 / 1), (154879630803 / 1000000000000), (154132293837 / 40000000000), (3853269017369 / 1000000000000), (154879156167 / 1000000000000)], ![(74600744949 / 125000000000), (596800339661 / 1000000000000), (1 / 1), (1 / 1), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![4, 3, 4, 0, 0], ![0, 3, -1, -1, 3], ![1, 1, 0, 0, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-2575152674099 / 1000000000000), (-1978893787617 / 1000000000000), (-257517175499 / 100000000000), (0 / 1), (0 / 1)], ![(0 / 1), (-1865107039219 / 1000000000000), (84308239401 / 62500000000), (674460941721 / 500000000000), (-1865110103771 / 1000000000000)], ![(-516163244231 / 1000000000000), (-129043165239 / 250000000000), (0 / 1), (0 / 1), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-1287576337049 / 500000000000), (-61840430863 / 31250000000), (-643792938747 / 250000000000), (0 / 1), (0 / 1)], ![(0 / 1), (-932553519609 / 500000000000), (1348931830417 / 1000000000000), (1348921883443 / 1000000000000), (-186511010377 / 100000000000)], ![(-51616324423 / 100000000000), (-103234532191 / 200000000000), (0 / 1), (0 / 1), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 22) : ℤ :=
  ([3, 8, 2, 2, 8, 3] : List ℤ).getD
    ((seed 0 22).splits.idxOf (sourceShape 0 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 22) : ℚ :=
  ([(-1742403451613 / 1000000000000), (-4956426022137 / 1000000000000), (-573067309077 / 500000000000), (-229227029681 / 200000000000), (-4956451455121 / 1000000000000), (-1742403168807 / 1000000000000)] : List ℚ).getD
    ((seed 0 22).splits.idxOf (sourceShape 0 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 22) : ℚ :=
  ([(-435600862903 / 250000000000), (-619553252767 / 125000000000), (-1146134618153 / 1000000000000), (-286533787101 / 250000000000), (-61955643189 / 12500000000), (-871201584403 / 500000000000)] : List ℚ).getD
    ((seed 0 22).splits.idxOf (sourceShape 0 c)) 0

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
        (splitWeight 0 22 0 c : ℝ) / 1000000000000) ≤
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
