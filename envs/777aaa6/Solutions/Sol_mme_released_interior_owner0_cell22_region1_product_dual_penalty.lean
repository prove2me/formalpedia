-- Prove2me | solution 1 for mme_released_interior_owner0_cell22_region1_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T12:37:20.334101+00:00
-- url     : https://prove2.me/submissions/f0aa93e7-08f1-46c7-86e3-e2062e78218f

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 22) : ℚ :=
  (splitWeight 0 22 1 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(116309962805000000000000000000000000 / 1525287929431747600536457049767280127), (19163201982400000000000000000000000 / 138662539039249781866950640887934557), (116309682431200000000000000000000000 / 1525287929431747600536457049767280127), (1 / 1), (1 / 1)], ![(1 / 1), (155271929709 / 1000000000000), (3844795084483 / 1000000000000), (3844790486851 / 1000000000000), (155271717219 / 1000000000000)], ![(59781922367 / 100000000000), (597818522271 / 1000000000000), (1 / 1), (1 / 1), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![4, 3, 4, 0, 0], ![0, 3, -1, -1, 3], ![1, 1, 0, 0, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-1286839878423 / 500000000000), (-1979051327947 / 1000000000000), (-2573682167423 / 1000000000000), (0 / 1), (0 / 1)], ![(0 / 1), (-93128865699 / 50000000000), (673360153757 / 500000000000), (1346719111707 / 1000000000000), (-465644670621 / 250000000000)], ![(-51446687229 / 100000000000), (-514468045553 / 1000000000000), (0 / 1), (0 / 1), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-514735951369 / 200000000000), (-989525663973 / 500000000000), (-1286841083711 / 500000000000), (0 / 1), (0 / 1)], ![(0 / 1), (-1862577313979 / 1000000000000), (269344061503 / 200000000000), (336679777927 / 250000000000), (-1862578682483 / 1000000000000)], ![(-514466872289 / 1000000000000), (-32154252847 / 62500000000), (0 / 1), (0 / 1), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 22) : ℤ :=
  ([3, 8, 2, 2, 8, 3] : List ℤ).getD
    ((seed 0 22).splits.idxOf (sourceShape 0 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 22) : ℚ :=
  ([(-1741428690689 / 1000000000000), (-4950725311621 / 1000000000000), (-1146799065987 / 1000000000000), (-1146799088527 / 1000000000000), (-990145505399 / 200000000000), (-1741428732197 / 1000000000000)] : List ℚ).getD
    ((seed 0 22).splits.idxOf (sourceShape 0 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 22) : ℚ :=
  ([(-6802455823 / 3906250000), (-247536265581 / 50000000000), (-573399532993 / 500000000000), (-573399544263 / 500000000000), (-2475363763497 / 500000000000), (-435357183049 / 250000000000)] : List ℚ).getD
    ((seed 0 22).splits.idxOf (sourceShape 0 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 22) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 22 =>
        (splitWeight 0 22 1 c : ℝ) / 1000000000000) ≤
          (1 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 22, ∏ i, weights i (c.val i) ≤ 1 := by
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
