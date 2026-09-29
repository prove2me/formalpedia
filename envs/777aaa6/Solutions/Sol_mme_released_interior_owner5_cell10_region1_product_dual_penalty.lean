-- Prove2me | solution 1 for mme_released_interior_owner5_cell10_region1_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-24T17:20:11.384902+00:00
-- url     : https://prove2.me/submissions/4fb61dbc-cb2a-4e51-a482-ddb51293db27

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 10) : ℚ :=
  (splitWeight 5 10 1 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(849668755857 / 1000000000000), (170098777083 / 200000000000), (1 / 1), (1 / 1), (1 / 1)], ![(425242925123 / 500000000000), (424885652349 / 500000000000), (1 / 1), (1 / 1), (1 / 1)], ![(1 / 1), (1 / 1), (74658718664125000000000000000000000 / 472288082208165027779644418414800059), (28011537150125000000000000000000000 / 52476453578685003086627157601644451), (24886025672875000000000000000000000 / 157429360736055009259881472804933353)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![1, 1, 0, 0, 0], ![1, 1, 0, 0, 0], ![0, 0, 3, 1, 3]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-81454352221 / 500000000000), (-161938056573 / 1000000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-40486876067 / 250000000000), (-40697004749 / 250000000000), (0 / 1), (0 / 1), (0 / 1)], ![(0 / 1), (0 / 1), (-368932366401 / 200000000000), (-313874049671 / 500000000000), (-1844670426423 / 1000000000000)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-162908704441 / 1000000000000), (-40484514143 / 250000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-161947504267 / 1000000000000), (-32557603799 / 200000000000), (0 / 1), (0 / 1), (0 / 1)], ![(0 / 1), (0 / 1), (-461165458001 / 250000000000), (-627748099341 / 1000000000000), (-922335213211 / 500000000000)]]

private def alphaScale (c : MME.ReleasedInterior.Split 10) : ℤ :=
  ([4, 2, 2, 4] : List ℤ).getD
    ((seed 5 10).splits.idxOf (sourceShape 5 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 10) : ℚ :=
  ([(-2169387907579 / 1000000000000), (-47581683009 / 50000000000), (-953444822779 / 1000000000000), (-2169526635137 / 1000000000000)] : List ℚ).getD
    ((seed 5 10).splits.idxOf (sourceShape 5 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 10) : ℚ :=
  ([(-1084693953789 / 500000000000), (-951633660179 / 1000000000000), (-476722411389 / 500000000000), (-16949426837 / 7812500000)] : List ℚ).getD
    ((seed 5 10).splits.idxOf (sourceShape 5 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 10) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 10 =>
        (splitWeight 5 10 1 c : ℝ) / 1000000000000) ≤
          (1 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 10, ∏ i, weights i (c.val i) ≤ 1 := by
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
