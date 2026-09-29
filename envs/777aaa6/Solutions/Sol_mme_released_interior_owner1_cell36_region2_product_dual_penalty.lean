-- Prove2me | solution 1 for mme_released_interior_owner1_cell36_region2_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T14:55:44.53876+00:00
-- url     : https://prove2.me/submissions/ac893291-8151-4dc5-82b2-a9c9acc7a57e

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 36) : ℚ :=
  (splitWeight 1 36 2 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(1 / 1), (78552173382500000000000000000000000 / 3788533422747233090771357931417353971), (1906239458094500000000000000000000000 / 3788533422747233090771357931417353971), (1906240644651500000000000000000000000 / 3788533422747233090771357931417353971), (78552214178000000000000000000000000 / 3788533422747233090771357931417353971)], ![(598949082887 / 1000000000000), (149737365861 / 250000000000), (1 / 1), (1 / 1), (1 / 1)], ![(292177477659 / 500000000000), (105066817637 / 100000000000), (29217783613 / 50000000000), (1 / 1), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![0, 6, 1, 1, 6], ![1, 1, 0, 0, 0], ![1, 0, 1, 0, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(0 / 1), (-775194246079 / 200000000000), (-686846553331 / 1000000000000), (-85855741359 / 125000000000), (-968992677763 / 250000000000)], ![(-64072336001 / 125000000000), (-512578052633 / 1000000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-134311670147 / 250000000000), (24713160113 / 500000000000), (-268622726847 / 500000000000), (0 / 1), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(0 / 1), (-1937985615197 / 500000000000), (-68684655333 / 100000000000), (-686845930871 / 1000000000000), (-3875970711051 / 1000000000000)], ![(-512578688007 / 1000000000000), (-64072256579 / 125000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-537246680587 / 1000000000000), (49426320227 / 1000000000000), (-537245453693 / 1000000000000), (0 / 1), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 36) : ℤ :=
  ([8, 2, 3, 3, 2, 8] : List ℤ).getD
    ((seed 1 36).splits.idxOf (sourceShape 1 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 36) : ℚ :=
  ([(-985158947359 / 200000000000), (-229999657147 / 200000000000), (-1736670695033 / 1000000000000), (-1736670664091 / 1000000000000), (-287499574663 / 250000000000), (-985159215929 / 200000000000)] : List ℚ).getD
    ((seed 1 36).splits.idxOf (sourceShape 1 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 36) : ℚ :=
  ([(-2462897368397 / 500000000000), (-574999142867 / 500000000000), (-217083836879 / 125000000000), (-173667066409 / 100000000000), (-1149998298651 / 1000000000000), (-1231449019911 / 250000000000)] : List ℚ).getD
    ((seed 1 36).splits.idxOf (sourceShape 1 c)) 0

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
        (splitWeight 1 36 2 c : ℝ) / 1000000000000) ≤
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
