-- Prove2me | solution 1 for mme_released_interior_owner0_cell31_region4_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T12:44:02.901529+00:00
-- url     : https://prove2.me/submissions/ea8ab365-f45c-4f07-bbe0-f85afbefa78e

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 31) : ℚ :=
  (splitWeight 0 31 4 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(53326714507000000000000000000000000 / 17609874533953620975836723218926238589), (2034230258188000000000000000000000000 / 17609874533953620975836723218926238589), (13133625199217000000000000000000000000 / 17609874533953620975836723218926238589), (2034226980068000000000000000000000000 / 17609874533953620975836723218926238589), (53326706625000000000000000000000000 / 17609874533953620975836723218926238589)], ![(98222363063 / 250000000000), (78577835071 / 200000000000), (1 / 1), (1 / 1), (1 / 1)], ![(136457888177 / 500000000000), (5759816601 / 4000000000), (1439953182807 / 1000000000000), (272914701751 / 1000000000000), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![9, 4, 1, 4, 9], ![2, 2, 0, 0, 0], ![2, 0, 0, 2, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-579977766089 / 100000000000), (-269792787743 / 125000000000), (-293284047099 / 1000000000000), (-86333756537 / 40000000000), (-724972226087 / 125000000000)], ![(-934226998663 / 1000000000000), (-467113851717 / 500000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-1298592042921 / 1000000000000), (22788204561 / 62500000000), (364610601119 / 1000000000000), (-649297990209 / 500000000000), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-5799777660889 / 1000000000000), (-2158342301943 / 1000000000000), (-146642023549 / 500000000000), (-134896494589 / 62500000000), (-1159955561739 / 200000000000)], ![(-467113499331 / 500000000000), (-934227703433 / 1000000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-32464801073 / 25000000000), (364611272977 / 1000000000000), (2278816257 / 6250000000), (-1298595980417 / 1000000000000), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 31) : ℤ :=
  ([12, 7, 4, 2, 2, 4, 7, 12] : List ℤ).getD
    ((seed 0 31).splits.idxOf (sourceShape 0 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 31) : ℚ :=
  ([(-8032601345777 / 1000000000000), (-4391165281031 / 1000000000000), (-2727959404257 / 1000000000000), (-5393127779 / 6250000000), (-862900477557 / 1000000000000), (-1363979819553 / 500000000000), (-1097790914951 / 250000000000), (-8032596849363 / 1000000000000)] : List ℚ).getD
    ((seed 0 31).splits.idxOf (sourceShape 0 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 31) : ℚ :=
  ([(-502037584111 / 62500000000), (-439116528103 / 100000000000), (-85248731383 / 31250000000), (-862900444639 / 1000000000000), (-215725119389 / 250000000000), (-545591927821 / 200000000000), (-4391163659803 / 1000000000000), (-4016298424681 / 500000000000)] : List ℚ).getD
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
        (splitWeight 0 31 4 c : ℝ) / 1000000000000) ≤
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
