-- Prove2me | solution 1 for mme_released_interior_owner0_cell21_region0_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T12:37:13.765145+00:00
-- url     : https://prove2.me/submissions/7b19877a-e31e-48fd-ab32-9f6dc2b1faab

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 21) : ℚ :=
  (splitWeight 0 21 0 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(201168486008500000000000000000000000 / 9989249579673820084245262882984805389), (420302237825000000000000000000000000 / 9989249579673820084245262882984805389), (201162250495500000000000000000000000 / 9989249579673820084245262882984805389), (1 / 1), (1 / 1)], ![(2435152903 / 62500000000), (2292099766691 / 1000000000000), (17113255968497 / 1000000000000), (2238308251 / 976562500), (3896241807 / 100000000000)], ![(418882275367 / 1000000000000), (775312296433 / 1000000000000), (52358690207 / 125000000000), (1 / 1), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![6, 5, 6, 0, 0], ![5, -1, -4, -1, 5], ![2, 1, 2, 0, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-3905121955891 / 1000000000000), (-3168290685323 / 1000000000000), (-3905152952841 / 1000000000000), (0 / 1), (0 / 1)], ![(-162257850417 / 50000000000), (829468326129 / 1000000000000), (283985336603 / 100000000000), (829436862053 / 1000000000000), (-3245157736683 / 1000000000000)], ![(-3480661457 / 4000000000), (-127244683829 / 500000000000), (-870195811719 / 1000000000000), (0 / 1), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-390512195589 / 100000000000), (-1584145342661 / 500000000000), (-97628823821 / 25000000000), (0 / 1), (0 / 1)], ![(-3245157008339 / 1000000000000), (82946832613 / 100000000000), (2839853366031 / 1000000000000), (414718431027 / 500000000000), (-1622578868341 / 500000000000)], ![(-870165364249 / 1000000000000), (-254489367657 / 1000000000000), (-435097905859 / 500000000000), (0 / 1), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 21) : ℤ :=
  ([3, 5, 12, 5, 1, 5, 12, 5, 3] : List ℤ).getD
    ((seed 0 21).splits.idxOf (sourceShape 0 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 21) : ℚ :=
  ([(-1935464395667 / 1000000000000), (-3330174485351 / 1000000000000), (-1604089011231 / 200000000000), (-3209018192049 / 1000000000000), (-145731671737 / 250000000000), (-1604509583199 / 500000000000), (-4010252885853 / 500000000000), (-133206958821 / 40000000000), (-1935464956977 / 1000000000000)] : List ℚ).getD
    ((seed 0 21).splits.idxOf (sourceShape 0 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 21) : ℚ :=
  ([(-967732197833 / 500000000000), (-66603489707 / 20000000000), (-4010222528077 / 500000000000), (-200563637003 / 62500000000), (-582926686947 / 1000000000000), (-3209019166397 / 1000000000000), (-1604101154341 / 200000000000), (-832543492631 / 250000000000), (-120966559811 / 62500000000)] : List ℚ).getD
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
        (splitWeight 0 21 0 c : ℝ) / 1000000000000) ≤
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
