-- Prove2me | solution 1 for mme_released_interior_owner1_cell21_region4_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T12:44:55.077601+00:00
-- url     : https://prove2.me/submissions/81902841-4a01-4a1f-b5d8-5bba4eb04f1b

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 21) : ℚ :=
  (splitWeight 1 21 4 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(2898925766200000000000000000000000 / 142483546182986711536258132470573519), (13790443050750000000000000000000000 / 332461607760302326917935642431338211), (20292479520100000000000000000000000 / 997384823280906980753806927294014633), (1 / 1), (1 / 1)], ![(38844053957 / 1000000000000), (1154224945791 / 500000000000), (1705767066863 / 100000000000), (1154224887357 / 500000000000), (7768810909 / 200000000000)], ![(51979419649 / 125000000000), (393692470073 / 500000000000), (103958832499 / 250000000000), (1 / 1), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![6, 5, 6, 0, 0], ![5, -1, -4, -1, 5], ![2, 1, 2, 0, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-194744314237 / 50000000000), (-63650971367 / 20000000000), (-1947443163149 / 500000000000), (0 / 1), (0 / 1)], ![(-1624100132591 / 500000000000), (418288128339 / 500000000000), (1418299997573 / 500000000000), (209144051513 / 250000000000), (-649640050009 / 200000000000)], ![(-438732936521 / 500000000000), (-239038026709 / 1000000000000), (-877465938443 / 1000000000000), (0 / 1), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-3894886284739 / 1000000000000), (-3182548568349 / 1000000000000), (-3894886326297 / 1000000000000), (0 / 1), (0 / 1)], ![(-3248200265181 / 1000000000000), (836576256679 / 1000000000000), (2836599995147 / 1000000000000), (836576206053 / 1000000000000), (-812050062511 / 250000000000)], ![(-877465873041 / 1000000000000), (-59759506677 / 250000000000), (-438732969221 / 500000000000), (0 / 1), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 21) : ℤ :=
  ([12, 5, 3, 5, 1, 5, 3, 5, 12] : List ℤ).getD
    ((seed 1 21).splits.idxOf (sourceShape 1 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 21) : ℚ :=
  ([(-16041104817 / 2000000000), (-824337026321 / 250000000000), (-967876114033 / 500000000000), (-3223438235429 / 1000000000000), (-58498659991 / 100000000000), (-161171912501 / 50000000000), (-1935752204167 / 1000000000000), (-1648674048221 / 500000000000), (-4010276265107 / 500000000000)] : List ℚ).getD
    ((seed 1 21).splits.idxOf (sourceShape 1 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 21) : ℚ :=
  ([(-8020552408499 / 1000000000000), (-3297348105283 / 1000000000000), (-387150445613 / 200000000000), (-805859558857 / 250000000000), (-584986599909 / 1000000000000), (-3223438250019 / 1000000000000), (-967876102083 / 500000000000), (-3297348096441 / 1000000000000), (-8020552530213 / 1000000000000)] : List ℚ).getD
    ((seed 1 21).splits.idxOf (sourceShape 1 c)) 0

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
        (splitWeight 1 21 4 c : ℝ) / 1000000000000) ≤
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
