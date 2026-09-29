-- Prove2me | solution 1 for mme_released_interior_owner3_cell11_region4_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T16:05:39.510798+00:00
-- url     : https://prove2.me/submissions/0266e340-f491-4614-a3c7-f5be4282b47e

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 11) : ℚ :=
  (splitWeight 3 11 4 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(59268719243 / 100000000000), (296344015783 / 500000000000), (1 / 1), (1 / 1), (1 / 1)], ![(22934606603 / 40000000000), (133568463373 / 125000000000), (5733667331 / 10000000000), (1 / 1), (1 / 1)], ![(1 / 1), (18879748654375000000000000000000000 / 967344191516556018590135121339730489), (490427888974750000000000000000000000 / 967344191516556018590135121339730489), (490428576422500000000000000000000000 / 967344191516556018590135121339730489), (18879719781500000000000000000000000 / 967344191516556018590135121339730489)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![1, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![0, 6, 1, 1, 6]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-6538606491 / 12500000000), (-104617420693 / 200000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-111246495781 / 200000000000), (33150221669 / 500000000000), (-556229744133 / 1000000000000), (0 / 1), (0 / 1)], ![(0 / 1), (-787292904349 / 200000000000), (-8490951459 / 12500000000), (-67927471499 / 100000000000), (-78729321021 / 20000000000)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-523088519279 / 1000000000000), (-65385887933 / 125000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-69529059863 / 125000000000), (66300443339 / 1000000000000), (-139057436033 / 250000000000), (0 / 1), (0 / 1)], ![(0 / 1), (-246029032609 / 62500000000), (-679276116719 / 1000000000000), (-679274714989 / 1000000000000), (-3936466051049 / 1000000000000)]]

private def alphaScale (c : MME.ReleasedInterior.Split 11) : ℤ :=
  ([8, 3, 2, 2, 3, 8] : List ℤ).getD
    ((seed 3 11).splits.idxOf (sourceShape 3 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 11) : ℚ :=
  ([(-5015781369459 / 1000000000000), (-1758594380131 / 1000000000000), (-1136062776847 / 1000000000000), (-113606279093 / 100000000000), (-1758594297357 / 1000000000000), (-2507893524639 / 500000000000)] : List ℚ).getD
    ((seed 3 11).splits.idxOf (sourceShape 3 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 11) : ℚ :=
  ([(-2507890684729 / 500000000000), (-175859438013 / 100000000000), (-568031388423 / 500000000000), (-1136062790929 / 1000000000000), (-439648574339 / 250000000000), (-5015787049277 / 1000000000000)] : List ℚ).getD
    ((seed 3 11).splits.idxOf (sourceShape 3 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 11) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 11 =>
        (splitWeight 3 11 4 c : ℝ) / 1000000000000) ≤
          (1 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 11, ∏ i, weights i (c.val i) ≤ 1 := by
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
