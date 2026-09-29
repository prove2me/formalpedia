-- Prove2me | solution 1 for mme_released_interior_owner1_cell25_region0_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T14:46:09.504996+00:00
-- url     : https://prove2.me/submissions/6242e420-158c-411a-93c2-6787fa8a9aa2

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 25) : ℚ :=
  (splitWeight 1 25 0 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(285428064825000000000000000000000000 / 17878956946484386280941261303999994099), (1366669256167000000000000000000000000 / 17878956946484386280941261303999994099), (1366665675088000000000000000000000000 / 17878956946484386280941261303999994099), (285425602584000000000000000000000000 / 17878956946484386280941261303999994099), (1 / 1)], ![(389983924929 / 1000000000000), (48747861947 / 125000000000), (1 / 1), (1 / 1), (1 / 1)], ![(52709891549 / 1000000000000), (1959850706917 / 1000000000000), (7196271589181 / 500000000000), (979920056877 / 500000000000), (52709893453 / 1000000000000)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![6, 4, 4, 6, 0], ![2, 2, 0, 0, 0], ![5, 0, -3, 0, 5]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-1034347418859 / 250000000000), (-2571247851921 / 1000000000000), (-2571250472221 / 1000000000000), (-2068699150979 / 500000000000), (0 / 1)], ![(-941649758839 / 1000000000000), (-470826199159 / 500000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-2942952145621 / 1000000000000), (672868300401 / 1000000000000), (2666710237623 / 1000000000000), (672862895299 / 1000000000000), (-2942952109499 / 1000000000000)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-827477935087 / 200000000000), (-32140598149 / 12500000000), (-128562523611 / 50000000000), (-4137398301957 / 1000000000000), (0 / 1)], ![(-470824879419 / 500000000000), (-941652398317 / 1000000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-147147607281 / 50000000000), (336434150201 / 500000000000), (333338779703 / 125000000000), (6728628953 / 10000000000), (-1471476054749 / 500000000000)]]

private def alphaScale (c : MME.ReleasedInterior.Split 25) : ℤ :=
  ([7, 12, 2, 5, 5, 2, 12, 7] : List ℤ).getD
    ((seed 1 25).splits.idxOf (sourceShape 1 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 25) : ℚ :=
  ([(-2203089589229 / 500000000000), (-8021991543783 / 1000000000000), (-423095006307 / 500000000000), (-1420017357729 / 500000000000), (-142001728507 / 50000000000), (-846189993437 / 1000000000000), (-401100142303 / 50000000000), (-2203089880213 / 500000000000)] : List ℚ).getD
    ((seed 1 25).splits.idxOf (sourceShape 1 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 25) : ℚ :=
  ([(-4406179178457 / 1000000000000), (-4010995771891 / 500000000000), (-846190012613 / 1000000000000), (-2840034715457 / 1000000000000), (-2840034570139 / 1000000000000), (-211547498359 / 250000000000), (-8022002846059 / 1000000000000), (-176247190417 / 40000000000)] : List ℚ).getD
    ((seed 1 25).splits.idxOf (sourceShape 1 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 25) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 25 =>
        (splitWeight 1 25 0 c : ℝ) / 1000000000000) ≤
          (1 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 25, ∏ i, weights i (c.val i) ≤ 1 := by
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
