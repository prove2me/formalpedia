-- Prove2me | solution 1 for mme_released_interior_owner1_cell19_region0_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T12:44:45.164529+00:00
-- url     : https://prove2.me/submissions/c4e4b142-3169-42b1-844d-4c37e324bac8

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 19) : ℚ :=
  (splitWeight 1 19 0 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(2005765809710000000000000000000000 / 101760028964526975996817812131168773), (4151139231595000000000000000000000 / 101760028964526975996817812131168773), (2005670577555000000000000000000000 / 101760028964526975996817812131168773), (1 / 1), (1 / 1)], ![(415431024821 / 1000000000000), (193485792369 / 250000000000), (415411289167 / 1000000000000), (1 / 1), (1 / 1)], ![(7789039579 / 200000000000), (2228816937907 / 1000000000000), (8924528425559 / 500000000000), (27858855407 / 12500000000), (3894517283 / 100000000000)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![6, 5, 6, 0, 0], ![2, 1, 2, 0, 0], ![5, -1, -4, -1, 5]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-1963295723207 / 500000000000), (-159961728701 / 50000000000), (-196331946337 / 50000000000), (0 / 1), (0 / 1)], ![(-13725604433 / 15625000000), (-128128416269 / 500000000000), (-219621547823 / 250000000000), (0 / 1), (0 / 1)], ![(-3245599803227 / 1000000000000), (801470923577 / 1000000000000), (2881950669357 / 1000000000000), (801422239459 / 1000000000000), (-405700055853 / 125000000000)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-3926591446413 / 1000000000000), (-3199234574019 / 1000000000000), (-3926638926739 / 1000000000000), (0 / 1), (0 / 1)], ![(-878438683711 / 1000000000000), (-256256832537 / 1000000000000), (-878486191291 / 1000000000000), (0 / 1), (0 / 1)], ![(-1622799901613 / 500000000000), (400735461789 / 500000000000), (1440975334679 / 500000000000), (40071111973 / 50000000000), (-3245600446823 / 1000000000000)]]

private def alphaScale (c : MME.ReleasedInterior.Split 19) : ℤ :=
  ([3, 5, 12, 5, 1, 5, 12, 5, 3] : List ℤ).getD
    ((seed 1 19).splits.idxOf (sourceShape 1 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 19) : ℚ :=
  ([(-1923126970169 / 1000000000000), (-67628520633 / 20000000000), (-8050630578809 / 1000000000000), (-81906245867 / 25000000000), (-573540737199 / 1000000000000), (-81906275633 / 25000000000), (-8050724922951 / 1000000000000), (-1690712421777 / 500000000000), (-1923126939269 / 1000000000000)] : List ℚ).getD
    ((seed 1 19).splits.idxOf (sourceShape 1 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 19) : ℚ :=
  ([(-240390871271 / 125000000000), (-3381426031649 / 1000000000000), (-1006328822351 / 125000000000), (-3276249834679 / 1000000000000), (-286770368599 / 500000000000), (-3276251025319 / 1000000000000), (-161014498459 / 20000000000), (-3381424843553 / 1000000000000), (-480781734817 / 250000000000)] : List ℚ).getD
    ((seed 1 19).splits.idxOf (sourceShape 1 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 19) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 19 =>
        (splitWeight 1 19 0 c : ℝ) / 1000000000000) ≤
          (1 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 19, ∏ i, weights i (c.val i) ≤ 1 := by
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
