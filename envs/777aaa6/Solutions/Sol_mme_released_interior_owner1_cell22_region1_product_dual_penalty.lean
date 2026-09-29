-- Prove2me | solution 1 for mme_released_interior_owner1_cell22_region1_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T14:54:26.508875+00:00
-- url     : https://prove2.me/submissions/82923d8d-7dfa-4f4e-94f5-9524409a7baa

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 22) : ℚ :=
  (splitWeight 1 22 1 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(290528124824500000000000000000000000 / 3816709174486733625167695701252354807), (527403751183000000000000000000000000 / 3816709174486733625167695701252354807), (290529054898000000000000000000000000 / 3816709174486733625167695701252354807), (1 / 1), (1 / 1)], ![(1 / 1), (30960537913 / 200000000000), (3854805213819 / 1000000000000), (770961935847 / 200000000000), (154806853141 / 1000000000000)], ![(119348635957 / 200000000000), (596744174651 / 1000000000000), (1 / 1), (1 / 1), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![4, 3, 4, 0, 0], ![0, 3, -1, -1, 3], ![1, 1, 0, 0, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-2575443470837 / 1000000000000), (-1979177471183 / 1000000000000), (-1287720134761 / 500000000000), (0 / 1), (0 / 1)], ![(0 / 1), (-1865603943527 / 1000000000000), (674660238773 / 500000000000), (337330408987 / 250000000000), (-186557704787 / 100000000000)], ![(-516268442761 / 1000000000000), (-516266775603 / 1000000000000), (0 / 1), (0 / 1), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-643860867709 / 250000000000), (-989588735591 / 500000000000), (-2575440269521 / 1000000000000), (0 / 1), (0 / 1)], ![(0 / 1), (-932801971763 / 500000000000), (1349320477547 / 1000000000000), (1349321635949 / 1000000000000), (-1865577047869 / 1000000000000)], ![(-12906711069 / 25000000000), (-258133387801 / 500000000000), (0 / 1), (0 / 1), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 22) : ℤ :=
  ([8, 3, 2, 2, 3, 8] : List ℤ).getD
    ((seed 1 22).splits.idxOf (sourceShape 1 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 22) : ℚ :=
  ([(-4957288961473 / 1000000000000), (-1742388610489 / 1000000000000), (-573062138997 / 500000000000), (-1146123769239 / 1000000000000), (-108899264671 / 62500000000), (-4957310988699 / 1000000000000)] : List ℚ).getD
    ((seed 1 22).splits.idxOf (sourceShape 1 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 22) : ℚ :=
  ([(-77457640023 / 15625000000), (-217798576311 / 125000000000), (-1146124277993 / 1000000000000), (-573061884619 / 500000000000), (-348477646947 / 200000000000), (-2478655494349 / 500000000000)] : List ℚ).getD
    ((seed 1 22).splits.idxOf (sourceShape 1 c)) 0

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
        (splitWeight 1 22 1 c : ℝ) / 1000000000000) ≤
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
