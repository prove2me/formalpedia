-- Prove2me | solution 1 for mme_released_interior_owner1_cell11_region5_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T12:44:29.841005+00:00
-- url     : https://prove2.me/submissions/bb3b2573-e214-458a-83f2-0cbfa9e76ac5

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 11) : ℚ :=
  (splitWeight 1 11 5 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(148175786096000000000000000000000000 / 1934469474668439746904960437663057051), (148175992419500000000000000000000000 / 1934469474668439746904960437663057051), (1 / 1), (1 / 1), (1 / 1)], ![(573385569641 / 1000000000000), (534292453123 / 500000000000), (143346809499 / 250000000000), (1 / 1), (1 / 1)], ![(1 / 1), (18884006921 / 125000000000), (784542879837 / 200000000000), (980680114941 / 250000000000), (75536073289 / 500000000000)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![4, 4, 0, 0, 0], ![1, 0, 1, 0, 0], ![0, 3, -1, -1, 3]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-20071789701 / 7812500000), (-513837537861 / 200000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-111239378431 / 200000000000), (2072976739 / 31250000000), (-278096991251 / 500000000000), (0 / 1), (0 / 1)], ![(0 / 1), (-944999184059 / 500000000000), (683391931471 / 500000000000), (1366785407937 / 1000000000000), (-1889997764367 / 1000000000000)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-2569189081727 / 1000000000000), (-321148461163 / 125000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-278098446077 / 500000000000), (66335255649 / 1000000000000), (-556193982501 / 1000000000000), (0 / 1), (0 / 1)], ![(0 / 1), (-1889998368117 / 1000000000000), (1366783862943 / 1000000000000), (683392703969 / 500000000000), (-944998882183 / 500000000000)]]

private def alphaScale (c : MME.ReleasedInterior.Split 11) : ℤ :=
  ([3, 2, 8, 8, 2, 3] : List ℤ).getD
    ((seed 1 11).splits.idxOf (sourceShape 1 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 11) : ℚ :=
  ([(-219824900161 / 125000000000), (-1136068418139 / 1000000000000), (-1003076747667 / 200000000000), (-1253845009993 / 250000000000), (-227213714143 / 200000000000), (-21982489669 / 12500000000)] : List ℚ).getD
    ((seed 1 11).splits.idxOf (sourceShape 1 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 11) : ℚ :=
  ([(-1758599201287 / 1000000000000), (-568034209069 / 500000000000), (-2507691869167 / 500000000000), (-5015380039971 / 1000000000000), (-568034285357 / 500000000000), (-1758599173519 / 1000000000000)] : List ℚ).getD
    ((seed 1 11).splits.idxOf (sourceShape 1 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 11) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 11 =>
        (splitWeight 1 11 5 c : ℝ) / 1000000000000) ≤
          (1 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 11, ∏ i, weights i (c.val i) ≤ 1 := by
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
