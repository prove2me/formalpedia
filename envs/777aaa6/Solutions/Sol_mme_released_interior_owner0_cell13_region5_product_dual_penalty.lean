-- Prove2me | solution 1 for mme_released_interior_owner0_cell13_region5_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T12:25:12.062953+00:00
-- url     : https://prove2.me/submissions/8289a3c5-abb7-4a2f-b7e1-f56428b38f23

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 13) : ℚ :=
  (splitWeight 0 13 5 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(78293650851600000000000000000000000 / 3547558421742617842352369850201126073), (78297527598200000000000000000000000 / 3547558421742617842352369850201126073), (1 / 1), (1 / 1), (1 / 1)], ![(53071104183 / 1000000000000), (400938261783 / 200000000000), (6799142665279 / 500000000000), (1002445464921 / 500000000000), (6633936299 / 125000000000)], ![(8643420487 / 31250000000), (353858628229 / 250000000000), (353876182879 / 250000000000), (55326094707 / 200000000000), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![6, 6, 0, 0, 0], ![5, -1, -3, -1, 5], ![2, 0, 0, 2, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-95338709127 / 25000000000), (-95337471271 / 25000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-1468061338099 / 500000000000), (86936261033 / 125000000000), (2609943706157 / 1000000000000), (695589660197 / 1000000000000), (-117444615961 / 40000000000)], ![(-321305245503 / 250000000000), (173718280111 / 500000000000), (34748616821 / 100000000000), (-642536346983 / 500000000000), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-3813548365079 / 1000000000000), (-3813498850839 / 1000000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-2936122676197 / 1000000000000), (139098017653 / 200000000000), (1304971853079 / 500000000000), (347794830099 / 500000000000), (-183507212439 / 62500000000)], ![(-1285220982011 / 1000000000000), (347436560223 / 1000000000000), (347486168211 / 1000000000000), (-257014538793 / 200000000000), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 13) : ℤ :=
  ([7, 2, 4, 12, 12, 4, 2, 7] : List ℤ).getD
    ((seed 0 13).splits.idxOf (sourceShape 0 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 13) : ℚ :=
  ([(-2201565485393 / 500000000000), (-85611849071 / 100000000000), (-2770522144667 / 1000000000000), (-803488474663 / 100000000000), (-32138776883 / 4000000000), (-2770522594361 / 1000000000000), (-856118584459 / 1000000000000), (-4403130172679 / 1000000000000)] : List ℚ).getD
    ((seed 0 13).splits.idxOf (sourceShape 0 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 13) : ℚ :=
  ([(-880626194157 / 200000000000), (-856118490709 / 1000000000000), (-1385261072333 / 500000000000), (-8034884746629 / 1000000000000), (-8034694220749 / 1000000000000), (-69263064859 / 25000000000), (-428059292229 / 500000000000), (-2201565086339 / 500000000000)] : List ℚ).getD
    ((seed 0 13).splits.idxOf (sourceShape 0 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 13) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 13 =>
        (splitWeight 0 13 5 c : ℝ) / 1000000000000) ≤
          (1 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 13, ∏ i, weights i (c.val i) ≤ 1 := by
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
