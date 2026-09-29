-- Prove2me | solution 1 for mme_released_interior_owner1_cell26_region2_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T14:54:29.794781+00:00
-- url     : https://prove2.me/submissions/b30e94cf-a900-4b1b-bd42-3a923d70b136

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 26) : ℚ :=
  (splitWeight 1 26 2 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(85588684463500000000000000000000000 / 8101920749517642671510703844037920187), (1195997613139000000000000000000000000 / 8101920749517642671510703844037920187), (1195981663228000000000000000000000000 / 8101920749517642671510703844037920187), (85585294067500000000000000000000000 / 8101920749517642671510703844037920187), (1 / 1)], ![(44365231277 / 100000000000), (212450507427 / 250000000000), (221820243219 / 500000000000), (1 / 1), (1 / 1)], ![(164438914401 / 1000000000000), (1558349489 / 625000000), (2493325835713 / 1000000000000), (5138518733 / 31250000000), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![7, 3, 3, 7, 0], ![2, 1, 2, 0, 0], ![3, -1, -1, 3, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-2275151679279 / 500000000000), (-382624100663 / 200000000000), (-478283459869 / 250000000000), (-4550342972009 / 1000000000000), (0 / 1)], ![(-101589262833 / 125000000000), (-162751862851 / 1000000000000), (-812740759777 / 1000000000000), (0 / 1), (0 / 1)], ![(-1805216118769 / 1000000000000), (913630870537 / 1000000000000), (456808748123 / 500000000000), (-180525452249 / 100000000000), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-4550303358557 / 1000000000000), (-956560251657 / 500000000000), (-76525353579 / 40000000000), (-568792871501 / 125000000000), (0 / 1)], ![(-812714102663 / 1000000000000), (-3255037257 / 20000000000), (-25398148743 / 31250000000), (0 / 1), (0 / 1)], ![(-112826007423 / 62500000000), (456815435269 / 500000000000), (913617496247 / 1000000000000), (-1805254522489 / 1000000000000), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 26) : ℤ :=
  ([7, 10, 3, 2, 7, 7, 2, 3, 10, 7] : List ℤ).getD
    ((seed 1 26).splits.idxOf (sourceShape 1 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 26) : ℚ :=
  ([(-4453047137589 / 1000000000000), (-202815725533 / 31250000000), (-1811713283449 / 1000000000000), (-290597473623 / 250000000000), (-4535018317891 / 1000000000000), (-4535019909993 / 1000000000000), (-581194928243 / 500000000000), (-452928334189 / 250000000000), (-3245052209493 / 500000000000), (-178121868587 / 40000000000)] : List ℚ).getD
    ((seed 1 26).splits.idxOf (sourceShape 1 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 26) : ℚ :=
  ([(-1113261784397 / 250000000000), (-1298020643411 / 200000000000), (-226464160431 / 125000000000), (-1162389894491 / 1000000000000), (-453501831789 / 100000000000), (-566877488749 / 125000000000), (-232477971297 / 200000000000), (-362342667351 / 200000000000), (-1298020883797 / 200000000000), (-2226523357337 / 500000000000)] : List ℚ).getD
    ((seed 1 26).splits.idxOf (sourceShape 1 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 26) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 26 =>
        (splitWeight 1 26 2 c : ℝ) / 1000000000000) ≤
          (1565 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 26, ∏ i, weights i (c.val i) ≤ 1 := by
    decide +kernel
  have h := mme_rational_product_dual_penalty_certificate alphaQ
    (fun c => (alpha_pos c).le) hprob weights weights_pos hmass weightLower alphaUpper
    (fun i j => (weight_logs i j).1) (fun c _ => (alpha_logs c).2)
    (1565 / 1000000000)
  have hbound : Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c => (alphaQ c : ℝ)) ≤ ((1565 / 1000000000 : ℚ) : ℝ) := by
    apply h
    decide +kernel
  simpa only [alphaQ, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat,
    Rat.cast_one, Rat.cast_zero] using hbound


#print axioms solution
