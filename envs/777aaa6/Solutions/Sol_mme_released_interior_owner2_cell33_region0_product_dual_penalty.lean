-- Prove2me | solution 1 for mme_released_interior_owner2_cell33_region0_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T16:09:43.796314+00:00
-- url     : https://prove2.me/submissions/983aae94-4e1b-4f90-ab39-c127c878aade

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 33) : ℚ :=
  (splitWeight 2 33 0 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(13331078591 / 250000000000), (1017130522177 / 500000000000), (6573140264623 / 500000000000), (508562921523 / 250000000000), (5332429453 / 100000000000)], ![(27385934928400000000000000000000000 / 1758757871077312988292982933759054029), (143583498257900000000000000000000000 / 1758757871077312988292982933759054029), (47861060158600000000000000000000000 / 586252623692437662764327644586351343), (27385728727900000000000000000000000 / 1758757871077312988292982933759054029), (1 / 1)], ![(78626902629 / 200000000000), (196566819129 / 500000000000), (1 / 1), (1 / 1), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![5, -1, -3, -1, 5], ![7, 4, 4, 7, 0], ![2, 2, 0, 0, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-366420359049 / 125000000000), (710132629781 / 1000000000000), (2576138869127 / 1000000000000), (355064014723 / 500000000000), (-1465681622171 / 500000000000)], ![(-4162333525983 / 1000000000000), (-626361587107 / 250000000000), (-626362140413 / 250000000000), (-2081170527721 / 500000000000), (0 / 1)], ![(-466801726521 / 500000000000), (-466802839229 / 500000000000), (0 / 1), (0 / 1), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-2931362872391 / 1000000000000), (355066314891 / 500000000000), (322017358641 / 125000000000), (710128029447 / 1000000000000), (-2931363244341 / 1000000000000)], ![(-2081166762991 / 500000000000), (-2505446348427 / 1000000000000), (-2505448561651 / 1000000000000), (-4162341055441 / 1000000000000), (0 / 1)], ![(-933603453041 / 1000000000000), (-933605678457 / 1000000000000), (0 / 1), (0 / 1), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 33) : ℤ :=
  ([7, 12, 2, 4, 4, 2, 12, 7] : List ℤ).getD
    ((seed 2 33).splits.idxOf (sourceShape 2 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 33) : ℚ :=
  ([(-2192905587511 / 500000000000), (-2006825055737 / 250000000000), (-862913157759 / 1000000000000), (-2728921772019 / 1000000000000), (-682230402581 / 250000000000), (-431456572783 / 500000000000), (-802730960637 / 100000000000), (-13705662121 / 3125000000)] : List ℚ).getD
    ((seed 2 33).splits.idxOf (sourceShape 2 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 33) : ℚ :=
  ([(-4385811175021 / 1000000000000), (-8027300222947 / 1000000000000), (-431456578879 / 500000000000), (-1364460886009 / 500000000000), (-2728921610323 / 1000000000000), (-172582629113 / 200000000000), (-8027309606369 / 1000000000000), (-4385811878719 / 1000000000000)] : List ℚ).getD
    ((seed 2 33).splits.idxOf (sourceShape 2 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 33) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 33 =>
        (splitWeight 2 33 0 c : ℝ) / 1000000000000) ≤
          (1 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 33, ∏ i, weights i (c.val i) ≤ 1 := by
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
