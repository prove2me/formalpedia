-- Prove2me | solution 1 for mme_released_interior_owner1_cell20_region2_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T12:44:48.390317+00:00
-- url     : https://prove2.me/submissions/a5585ea2-1cfc-448c-bbd5-5c568cb82484

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 20) : ℚ :=
  (splitWeight 1 20 2 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(27783376269062500000000000000000000 / 994768280392088368018504794197147299), (53989517114375000000000000000000000 / 994768280392088368018504794197147299), (27780245040812500000000000000000000 / 994768280392088368018504794197147299), (1 / 1), (1 / 1)], ![(21949291757 / 125000000000), (2352843551917 / 1000000000000), (470543103961 / 200000000000), (21944415771 / 125000000000), (1 / 1)], ![(168414105121 / 1000000000000), (245754475683 / 100000000000), (2457401823793 / 1000000000000), (84198006829 / 500000000000), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![6, 5, 6, 0, 0], ![3, -1, -1, 3, 0], ![3, -1, -1, 3, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-715614392021 / 200000000000), (-1456859962901 / 500000000000), (-1789092333979 / 500000000000), (0 / 1), (0 / 1)], ![(-869789432249 / 500000000000), (855624618761 / 1000000000000), (6844561611 / 8000000000), (-1739801036937 / 1000000000000), (0 / 1)], ![(-6958318051 / 3906250000), (179832557043 / 200000000000), (449552311307 / 500000000000), (-1781436849319 / 1000000000000), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-447258995013 / 125000000000), (-2913719925801 / 1000000000000), (-3578184667957 / 1000000000000), (0 / 1), (0 / 1)], ![(-1739578864497 / 1000000000000), (427812309381 / 500000000000), (26736568793 / 31250000000), (-217475129617 / 125000000000), (0 / 1)], ![(-356265884211 / 200000000000), (14049418519 / 15625000000), (179820924523 / 200000000000), (-890718424659 / 500000000000), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 20) : ℤ :=
  ([7, 3, 7, 10, 2, 2, 10, 7, 3, 7] : List ℤ).getD
    ((seed 1 20).splits.idxOf (sourceShape 1 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 20) : ℚ :=
  ([(-2210278472347 / 500000000000), (-455780448707 / 250000000000), (-281618471017 / 62500000000), (-802636329957 / 125000000000), (-289764449551 / 250000000000), (-1159061534499 / 1000000000000), (-6420975691937 / 1000000000000), (-901191018477 / 200000000000), (-1823121922663 / 1000000000000), (-4420505787543 / 1000000000000)] : List ℚ).getD
    ((seed 1 20).splits.idxOf (sourceShape 1 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 20) : ℚ :=
  ([(-4420556944693 / 1000000000000), (-1823121794827 / 1000000000000), (-4505895536271 / 1000000000000), (-1284218127931 / 200000000000), (-1159057798203 / 1000000000000), (-579530767249 / 500000000000), (-200655490373 / 31250000000), (-140811096637 / 31250000000), (-911560961331 / 500000000000), (-2210252893771 / 500000000000)] : List ℚ).getD
    ((seed 1 20).splits.idxOf (sourceShape 1 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 20) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 20 =>
        (splitWeight 1 20 2 c : ℝ) / 1000000000000) ≤
          (407 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 20, ∏ i, weights i (c.val i) ≤ 1 := by
    decide +kernel
  have h := mme_rational_product_dual_penalty_certificate alphaQ
    (fun c => (alpha_pos c).le) hprob weights weights_pos hmass weightLower alphaUpper
    (fun i j => (weight_logs i j).1) (fun c _ => (alpha_logs c).2)
    (407 / 1000000000)
  have hbound : Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c => (alphaQ c : ℝ)) ≤ ((407 / 1000000000 : ℚ) : ℝ) := by
    apply h
    decide +kernel
  simpa only [alphaQ, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat,
    Rat.cast_one, Rat.cast_zero] using hbound


#print axioms solution
