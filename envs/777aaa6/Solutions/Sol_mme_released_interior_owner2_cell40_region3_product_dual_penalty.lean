-- Prove2me | solution 1 for mme_released_interior_owner2_cell40_region3_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T16:16:07.240631+00:00
-- url     : https://prove2.me/submissions/c6fa4e63-d8df-46ea-8659-6f0b9248b3c6

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 40) : ℚ :=
  (splitWeight 2 40 3 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(1 / 1), (1 / 1), (609071286883 / 1000000000000), (1959556253969 / 1000000000000), (38078559453 / 62500000000)], ![(170578367881000000000000000000000000 / 747410008118931132355083247657005597), (56860853615800000000000000000000000 / 249136669372977044118361082552335199), (1 / 1), (1 / 1), (1 / 1)], ![(852862729393 / 1000000000000), (852877085421 / 1000000000000), (1 / 1), (1 / 1), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![0, 0, 1, 0, 1], ![3, 3, 0, 0, 0], ![1, 1, 0, 0, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(0 / 1), (0 / 1), (-247909981243 / 500000000000), (672718046573 / 1000000000000), (-247757588513 / 500000000000)], ![(-92338692547 / 62500000000), (-738697250087 / 500000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-2486822989 / 15625000000), (-39784959671 / 250000000000), (0 / 1), (0 / 1), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(0 / 1), (0 / 1), (-99163992497 / 200000000000), (336359023287 / 500000000000), (-19820607081 / 40000000000)], ![(-1477419080751 / 1000000000000), (-1477394500173 / 1000000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-31831334259 / 200000000000), (-159139838683 / 1000000000000), (0 / 1), (0 / 1), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 40) : ℤ :=
  ([2, 4, 4, 2] : List ℤ).getD
    ((seed 2 40).splits.idxOf (sourceShape 2 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 40) : ℚ :=
  ([(-963840872863 / 1000000000000), (-85283637163 / 40000000000), (-2132354301347 / 1000000000000), (-481916562447 / 500000000000)] : List ℚ).getD
    ((seed 2 40).splits.idxOf (sourceShape 2 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 40) : ℚ :=
  ([(-481920436431 / 500000000000), (-1066045464537 / 500000000000), (-1066177150673 / 500000000000), (-963833124893 / 1000000000000)] : List ℚ).getD
    ((seed 2 40).splits.idxOf (sourceShape 2 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 40) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 40 =>
        (splitWeight 2 40 3 c : ℝ) / 1000000000000) ≤
          (1 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 40, ∏ i, weights i (c.val i) ≤ 1 := by
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
