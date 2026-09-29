-- Prove2me | solution 1 for mme_released_interior_owner1_cell12_region1_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T12:44:30.631872+00:00
-- url     : https://prove2.me/submissions/c16dbe76-ecf0-477b-8dc0-fa3a1e0caa65

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 12) : ℚ :=
  (splitWeight 1 12 1 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(12225447231406250000000000000000000 / 555099998148046773379067367860880403), (12225012635812500000000000000000000 / 555099998148046773379067367860880403), (1 / 1), (1 / 1), (1 / 1)], ![(139239972411 / 500000000000), (1404945318017 / 1000000000000), (280979247751 / 200000000000), (278440141227 / 1000000000000), (1 / 1)], ![(5320417013 / 100000000000), (1985033863603 / 1000000000000), (172134201943 / 12500000000), (1984882856573 / 1000000000000), (13301005187 / 250000000000)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![6, 6, 0, 0, 0], ![2, 0, 0, 2, 0], ![5, 0, -3, 0, 5]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-1907814328161 / 500000000000), (-953916051349 / 250000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-1278409233619 / 1000000000000), (339998382467 / 1000000000000), (169981724319 / 500000000000), (-639276087737 / 500000000000), (0 / 1)], ![(-586723699961 / 200000000000), (685635973743 / 1000000000000), (2622545772127 / 1000000000000), (171389974519 / 250000000000), (-2933621307521 / 1000000000000)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-3815628656321 / 1000000000000), (-763132841079 / 200000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-639204616809 / 500000000000), (84999595617 / 250000000000), (339963448639 / 1000000000000), (-1278552175473 / 1000000000000), (0 / 1)], ![(-733404624951 / 250000000000), (42852248359 / 62500000000), (81954555379 / 31250000000), (685559898077 / 1000000000000), (-4583783293 / 1562500000)]]

private def alphaScale (c : MME.ReleasedInterior.Split 12) : ℤ :=
  ([7, 2, 5, 12, 12, 5, 2, 7] : List ℤ).getD
    ((seed 1 12).splits.idxOf (sourceShape 1 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 12) : ℚ :=
  ([(-4408544858049 / 1000000000000), (-853119435553 / 1000000000000), (-558014075157 / 200000000000), (-8027659196199 / 1000000000000), (-8027834881389 / 1000000000000), (-2790064783023 / 1000000000000), (-853120050801 / 1000000000000), (-4408513540967 / 1000000000000)] : List ℚ).getD
    ((seed 1 12).splits.idxOf (sourceShape 1 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 12) : ℚ :=
  ([(-4408544858047 / 1000000000000), (-26659982361 / 31250000000), (-348758796973 / 125000000000), (-4013829598099 / 500000000000), (-2006958720347 / 250000000000), (-1395032391511 / 500000000000), (-2132800127 / 2500000000), (-2204256770483 / 500000000000)] : List ℚ).getD
    ((seed 1 12).splits.idxOf (sourceShape 1 c)) 0

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
        (splitWeight 1 12 1 c : ℝ) / 1000000000000) ≤
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
