-- Prove2me | solution 1 for mme_released_interior_owner4_cell37_region1_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-24T17:19:20.966685+00:00
-- url     : https://prove2.me/submissions/a5ca7156-af95-4e2d-a72d-e62bfe0e3a2a

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 37) : ℚ :=
  (splitWeight 4 37 1 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(1 / 1), (19630404951 / 125000000000), (3813566020941 / 1000000000000), (953391716003 / 250000000000), (31409626413 / 200000000000)], ![(292129372864000000000000000000000000 / 3789346299514672828541409549622099183), (525411530114500000000000000000000000 / 3789346299514672828541409549622099183), (292129798894500000000000000000000000 / 3789346299514672828541409549622099183), (1 / 1), (1 / 1)], ![(598892832233 / 1000000000000), (119778665013 / 200000000000), (1 / 1), (1 / 1), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![0, 3, -1, -1, 3], ![4, 3, 4, 0, 0], ![1, 1, 0, 0, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(0 / 1), (-1851234100037 / 1000000000000), (1338564714899 / 1000000000000), (1338564935971 / 1000000000000), (-462800736739 / 250000000000)], ![(-2562752040961 / 1000000000000), (-61742718139 / 31250000000), (-2562750582599 / 1000000000000), (0 / 1), (0 / 1)], ![(-128168152001 / 250000000000), (-512671785099 / 1000000000000), (0 / 1), (0 / 1), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(0 / 1), (-462808525009 / 250000000000), (13385647149 / 10000000000), (334641233993 / 250000000000), (-370240589391 / 200000000000)], ![(-125134377 / 48828125), (-1975766980447 / 1000000000000), (-1281375291299 / 500000000000), (0 / 1), (0 / 1)], ![(-512672608003 / 1000000000000), (-256335892549 / 500000000000), (0 / 1), (0 / 1), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 37) : ℤ :=
  ([8, 3, 2, 2, 3, 8] : List ℤ).getD
    ((seed 4 37).splits.idxOf (sourceShape 4 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 37) : ℚ :=
  ([(-39413020767 / 8000000000), (-1736858890087 / 1000000000000), (-574937326241 / 500000000000), (-1149874050647 / 1000000000000), (-1736858475707 / 1000000000000), (-2463328233841 / 500000000000)] : List ℚ).getD
    ((seed 4 37).splits.idxOf (sourceShape 4 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 37) : ℚ :=
  ([(-2463313797937 / 500000000000), (-868429445043 / 500000000000), (-1149874652481 / 1000000000000), (-574937025323 / 500000000000), (-868429237853 / 500000000000), (-4926656467681 / 1000000000000)] : List ℚ).getD
    ((seed 4 37).splits.idxOf (sourceShape 4 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 37) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 37 =>
        (splitWeight 4 37 1 c : ℝ) / 1000000000000) ≤
          (1 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 37, ∏ i, weights i (c.val i) ≤ 1 := by
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
