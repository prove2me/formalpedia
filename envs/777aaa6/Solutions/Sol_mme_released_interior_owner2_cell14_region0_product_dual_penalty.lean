-- Prove2me | solution 1 for mme_released_interior_owner2_cell14_region0_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T15:17:04.475576+00:00
-- url     : https://prove2.me/submissions/15663c49-db8e-4785-913e-039bae1f5aa3

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 14) : ℚ :=
  (splitWeight 2 14 0 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(299214810321 / 500000000000), (598430048993 / 1000000000000), (1 / 1), (1 / 1), (1 / 1)], ![(1 / 1), (155955863832000000000000000000000000 / 7605895997615316513048025295490533753), (3833333690635000000000000000000000000 / 7605895997615316513048025295490533753), (547619536418000000000000000000000000 / 1086556571087902359006860756498647679), (155955734672000000000000000000000000 / 7605895997615316513048025295490533753)], ![(58313457727 / 100000000000), (1050933772367 / 1000000000000), (291567797217 / 500000000000), (1 / 1), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![1, 1, 0, 0, 0], ![0, 6, 1, 1, 6], ![1, 0, 1, 0, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-513446353811 / 1000000000000), (-25672281901 / 50000000000), (0 / 1), (0 / 1), (0 / 1)], ![(0 / 1), (-3887105971601 / 1000000000000), (-342594447887 / 500000000000), (-342594048197 / 500000000000), (-485888349973 / 125000000000)], ![(-539337283473 / 1000000000000), (24839537993 / 500000000000), (-539335539171 / 1000000000000), (0 / 1), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-51344635381 / 100000000000), (-513445638019 / 1000000000000), (0 / 1), (0 / 1), (0 / 1)], ![(0 / 1), (-9717764929 / 2500000000), (-685188895773 / 1000000000000), (-685188096393 / 1000000000000), (-3887106799783 / 1000000000000)], ![(-33708580217 / 62500000000), (49679075987 / 1000000000000), (-53933553917 / 100000000000), (0 / 1), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 14) : ℤ :=
  ([8, 3, 2, 2, 3, 8] : List ℤ).getD
    ((seed 2 14).splits.idxOf (sourceShape 2 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 14) : ℚ :=
  ([(-987977429757 / 200000000000), (-1737970788757 / 1000000000000), (-1148955457807 / 1000000000000), (-229791074843 / 200000000000), (-1737971017889 / 1000000000000), (-4939890437073 / 1000000000000)] : List ℚ).getD
    ((seed 2 14).splits.idxOf (sourceShape 2 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 14) : ℚ :=
  ([(-308742946799 / 62500000000), (-434492697189 / 250000000000), (-574477728903 / 500000000000), (-574477687107 / 500000000000), (-54311594309 / 31250000000), (-308743152317 / 62500000000)] : List ℚ).getD
    ((seed 2 14).splits.idxOf (sourceShape 2 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 14) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 14 =>
        (splitWeight 2 14 0 c : ℝ) / 1000000000000) ≤
          (1 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 14, ∏ i, weights i (c.val i) ≤ 1 := by
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
