-- Prove2me | solution 1 for mme_released_interior_owner2_cell25_region3_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T15:40:34.236297+00:00
-- url     : https://prove2.me/submissions/ae4f8b02-5951-4fb7-8ffd-b4e847c3c9ea

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 25) : ℚ :=
  (splitWeight 2 25 3 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(28552050829 / 100000000000), (273271270691 / 200000000000), (170793573981 / 125000000000), (28551575249 / 100000000000), (1 / 1)], ![(77995984603000000000000000000000000 / 3575830602918496302136150595225080543), (77995543069000000000000000000000000 / 3575830602918496302136150595225080543), (1 / 1), (1 / 1), (1 / 1)], ![(52703306233 / 1000000000000), (490001041147 / 250000000000), (7198191456209 / 500000000000), (1959981896981 / 1000000000000), (26351625263 / 500000000000)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![2, 0, 0, 2, 0], ![6, 6, 0, 0, 0], ![5, 0, -3, 0, 5]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-1253441419577 / 1000000000000), (78036900203 / 250000000000), (156070960141 / 500000000000), (-156682259539 / 125000000000), (0 / 1)], ![(-956323854677 / 250000000000), (-3825301079707 / 1000000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-1471538544267 / 500000000000), (672946598029 / 1000000000000), (2666976988391 / 1000000000000), (134587047393 / 200000000000), (-2943078145527 / 1000000000000)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-156680177447 / 125000000000), (312147600813 / 1000000000000), (312141920283 / 1000000000000), (-1253458076311 / 1000000000000), (0 / 1)], ![(-3825295418707 / 1000000000000), (-1912650539853 / 500000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-2943077088533 / 1000000000000), (67294659803 / 100000000000), (333372123549 / 125000000000), (336467618483 / 500000000000), (-1471539072763 / 500000000000)]]

private def alphaScale (c : MME.ReleasedInterior.Split 25) : ℤ :=
  ([12, 5, 2, 7, 7, 2, 5, 12] : List ℤ).getD
    ((seed 2 25).splits.idxOf (sourceShape 2 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 25) : ℚ :=
  ([(-8021814984001 / 1000000000000), (-2840212580933 / 1000000000000), (-846176510033 / 1000000000000), (-4405806897001 / 1000000000000), (-881161452461 / 200000000000), (-423088245251 / 500000000000), (-14201062807 / 5000000000), (-4010918122057 / 500000000000)] : List ℚ).getD
    ((seed 2 25).splits.idxOf (sourceShape 2 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 25) : ℚ :=
  ([(-1002726873 / 125000000), (-710053145233 / 250000000000), (-52886031877 / 62500000000), (-4405806897 / 1000000000), (-137681476947 / 31250000000), (-846176490501 / 1000000000000), (-2840212561399 / 1000000000000), (-8021836244113 / 1000000000000)] : List ℚ).getD
    ((seed 2 25).splits.idxOf (sourceShape 2 c)) 0

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
        (splitWeight 2 25 3 c : ℝ) / 1000000000000) ≤
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
