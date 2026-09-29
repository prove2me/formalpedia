-- Prove2me | solution 1 for mme_released_interior_owner0_cell21_region1_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T12:37:15.053143+00:00
-- url     : https://prove2.me/submissions/f47795f0-a0fb-431f-9aa2-b877a3a3d538

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 21) : ℚ :=
  (splitWeight 0 21 1 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(205583873781000000000000000000000000 / 9916175202728135299624294736555998427), (405402873200000000000000000000000000 / 9916175202728135299624294736555998427), (205564327923000000000000000000000000 / 9916175202728135299624294736555998427), (1 / 1), (1 / 1)], ![(974632523 / 25000000000), (1155762229029 / 500000000000), (8443055452937 / 500000000000), (2311302442561 / 1000000000000), (7797039653 / 200000000000)], ![(412786630619 / 1000000000000), (20107311983 / 25000000000), (412747618601 / 1000000000000), (1 / 1), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![6, 5, 6, 0, 0], ![5, -1, -4, -1, 5], ![2, 1, 2, 0, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-1938034233051 / 500000000000), (-25576329923 / 8000000000), (-1938081772741 / 500000000000), (0 / 1), (0 / 1)], ![(-648914120677 / 200000000000), (837907245423 / 1000000000000), (176655715259 / 62500000000), (83781119359 / 100000000000), (-40557165457 / 12500000000)], ![(-442412226203 / 500000000000), (-217792295707 / 1000000000000), (-884918965791 / 1000000000000), (0 / 1), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-3876068466101 / 1000000000000), (-1598520620187 / 500000000000), (-3876163545481 / 1000000000000), (0 / 1), (0 / 1)], ![(-405571325423 / 125000000000), (52369202839 / 62500000000), (565298288829 / 200000000000), (837811193591 / 1000000000000), (-3244573236559 / 1000000000000)], ![(-176964890481 / 200000000000), (-108896147853 / 500000000000), (-88491896579 / 100000000000), (0 / 1), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 21) : ℤ :=
  ([3, 5, 12, 5, 1, 5, 12, 5, 3] : List ℤ).getD
    ((seed 0 21).splits.idxOf (sourceShape 0 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 21) : ℚ :=
  ([(-483623996483 / 250000000000), (-3256049575041 / 1000000000000), (-8005466157043 / 1000000000000), (-648810593493 / 200000000000), (-294171045967 / 500000000000), (-3244054492457 / 1000000000000), (-2001413278983 / 250000000000), (-1628024294479 / 500000000000), (-1934496555563 / 1000000000000)] : List ℚ).getD
    ((seed 0 21).splits.idxOf (sourceShape 0 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 21) : ℚ :=
  ([(-1934495985931 / 1000000000000), (-5087577461 / 1562500000), (-4002733078521 / 500000000000), (-405506620933 / 125000000000), (-588342091933 / 1000000000000), (-405506811557 / 125000000000), (-8005653115931 / 1000000000000), (-3256048588957 / 1000000000000), (-967248277781 / 500000000000)] : List ℚ).getD
    ((seed 0 21).splits.idxOf (sourceShape 0 c)) 0

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
        (splitWeight 0 21 1 c : ℝ) / 1000000000000) ≤
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
