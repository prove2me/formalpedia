-- Prove2me | solution 1 for mme_released_interior_owner0_cell12_region3_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T12:25:09.136831+00:00
-- url     : https://prove2.me/submissions/e9a67321-414e-4dfa-9d4a-1e14b76122c6

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 12) : ℚ :=
  (splitWeight 0 12 3 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(1948185978900000000000000000000000 / 89553525178151841859340744541581689), (1948190033900000000000000000000000 / 89553525178151841859340744541581689), (1 / 1), (1 / 1), (1 / 1)], ![(56805483119 / 200000000000), (1372254068063 / 1000000000000), (686128428337 / 500000000000), (8875931903 / 31250000000), (1 / 1)], ![(3294080241 / 62500000000), (1959685870497 / 1000000000000), (7186353637981 / 500000000000), (78387779659 / 40000000000), (5270531611 / 100000000000)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![6, 6, 0, 0, 0], ![2, 0, 0, 2, 0], ![5, 0, -3, 0, 5]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-956984455207 / 250000000000), (-3827935739407 / 1000000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-251736902339 / 200000000000), (316454692963 / 1000000000000), (3164567251 / 10000000000), (-1258676043179 / 1000000000000), (0 / 1)], ![(-2943039565539 / 1000000000000), (672784190243 / 1000000000000), (666332770029 / 250000000000), (168197147349 / 250000000000), (-294303895357 / 100000000000)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-3827937820827 / 1000000000000), (-1913967869703 / 500000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-629342255847 / 500000000000), (79113673241 / 250000000000), (316456725101 / 1000000000000), (-629338021589 / 500000000000), (0 / 1)], ![(-1471519782769 / 500000000000), (168196047561 / 250000000000), (2665331080117 / 1000000000000), (672788589397 / 1000000000000), (-2943038953569 / 1000000000000)]]

private def alphaScale (c : MME.ReleasedInterior.Split 12) : ℤ :=
  ([12, 5, 2, 7, 7, 2, 5, 12] : List ℤ).getD
    ((seed 0 12).splits.idxOf (sourceShape 0 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 12) : ℚ :=
  ([(-8029661283953 / 1000000000000), (-709673634617 / 250000000000), (-846150015611 / 1000000000000), (-4413829673769 / 1000000000000), (-4413831661677 / 1000000000000), (-846149966329 / 1000000000000), (-567738964813 / 200000000000), (-8029651347213 / 1000000000000)] : List ℚ).getD
    ((seed 0 12).splits.idxOf (sourceShape 0 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 12) : ℚ :=
  ([(-501853830247 / 62500000000), (-2838694538467 / 1000000000000), (-84615001561 / 100000000000), (-551728709221 / 125000000000), (-1103457915419 / 250000000000), (-105768745791 / 125000000000), (-22177303313 / 7812500000), (-2007412836803 / 250000000000)] : List ℚ).getD
    ((seed 0 12).splits.idxOf (sourceShape 0 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 12) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 12 =>
        (splitWeight 0 12 3 c : ℝ) / 1000000000000) ≤
          (1 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 12, ∏ i, weights i (c.val i) ≤ 1 := by
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
