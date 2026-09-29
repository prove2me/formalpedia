-- Prove2me | solution 1 for mme_released_interior_owner0_cell21_region2_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T12:37:16.264062+00:00
-- url     : https://prove2.me/submissions/74017d0c-b864-44f5-b424-ae933742aa5c

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 21) : ℚ :=
  (splitWeight 0 21 2 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(2600427344000000000000000000000000 / 127908473972014549726569612252648011), (5299141295000000000000000000000000 / 127908473972014549726569612252648011), (2600600400500000000000000000000000 / 127908473972014549726569612252648011), (1 / 1), (1 / 1)], ![(19433546709 / 500000000000), (577418925101 / 250000000000), (2133414682793 / 125000000000), (1154915244847 / 500000000000), (2429199609 / 62500000000)], ![(83176730973 / 200000000000), (787907570987 / 1000000000000), (16636462583 / 40000000000), (1 / 1), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![6, 5, 6, 0, 0], ![5, -1, -4, -1, 5], ![2, 1, 2, 0, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-194781958323 / 50000000000), (-1591885086719 / 500000000000), (-194778630971 / 50000000000), (0 / 1), (0 / 1)], ![(-649521462783 / 200000000000), (418553562621 / 500000000000), (2837165375209 / 1000000000000), (209293535189 / 250000000000), (-162380236633 / 50000000000)], ![(-877349733643 / 1000000000000), (-119187245853 / 500000000000), (-877282626477 / 1000000000000), (0 / 1), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-3895639166459 / 1000000000000), (-3183770173437 / 1000000000000), (-3895572619419 / 1000000000000), (0 / 1), (0 / 1)], ![(-1623803656957 / 500000000000), (837107125243 / 1000000000000), (283716537521 / 100000000000), (837174140757 / 1000000000000), (-3247604732659 / 1000000000000)], ![(-438674866821 / 500000000000), (-47674898341 / 200000000000), (-219320656619 / 250000000000), (0 / 1), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 21) : ℤ :=
  ([3, 5, 12, 5, 1, 5, 12, 5, 3] : List ℤ).getD
    ((seed 0 21).splits.idxOf (sourceShape 0 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 21) : ℚ :=
  ([(-1935756417793 / 1000000000000), (-3296839517179 / 1000000000000), (-8020593633987 / 1000000000000), (-644789134893 / 200000000000), (-584979289929 / 1000000000000), (-805986441639 / 250000000000), (-8020462559989 / 1000000000000), (-1648419993063 / 500000000000), (-1935756977797 / 1000000000000)] : List ℚ).getD
    ((seed 0 21).splits.idxOf (sourceShape 0 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 21) : ℚ :=
  ([(-7561548507 / 3906250000), (-1648419758589 / 500000000000), (-4010296816993 / 500000000000), (-100748302327 / 31250000000), (-73122411241 / 125000000000), (-644789153311 / 200000000000), (-2005115639997 / 250000000000), (-26374719889 / 8000000000), (-483939244449 / 250000000000)] : List ℚ).getD
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
        (splitWeight 0 21 2 c : ℝ) / 1000000000000) ≤
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
