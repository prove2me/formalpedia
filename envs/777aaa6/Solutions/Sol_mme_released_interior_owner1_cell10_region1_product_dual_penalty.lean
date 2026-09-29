-- Prove2me | solution 1 for mme_released_interior_owner1_cell10_region1_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T12:44:24.449111+00:00
-- url     : https://prove2.me/submissions/1a5c4190-279c-415e-83ee-72bcd27936d5

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 10) : ℚ :=
  (splitWeight 1 10 1 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(84860480713300000000000000000000000 / 377313921547453762458719144012030449), (84895880962200000000000000000000000 / 377313921547453762458719144012030449), (1 / 1), (1 / 1), (1 / 1)], ![(850722770021 / 1000000000000), (5318341967 / 6250000000), (1 / 1), (1 / 1), (1 / 1)], ![(1 / 1), (1 / 1), (598607528843 / 1000000000000), (2011551065387 / 1000000000000), (37689440637 / 62500000000)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![3, 3, 0, 0, 0], ![1, 1, 0, 0, 0], ![0, 0, 1, -1, 1]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-1492069019571 / 1000000000000), (-372912987079 / 250000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-80834486571 / 500000000000), (-16141986931 / 100000000000), (0 / 1), (0 / 1), (0 / 1)], ![(0 / 1), (0 / 1), (-32071819139 / 62500000000), (139781219761 / 200000000000), (-20231463629 / 40000000000)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-149206901957 / 100000000000), (-298330389663 / 200000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-161668973141 / 1000000000000), (-161419869309 / 1000000000000), (0 / 1), (0 / 1), (0 / 1)], ![(0 / 1), (0 / 1), (-513149106223 / 1000000000000), (349453049403 / 500000000000), (-126446647681 / 250000000000)]]

private def alphaScale (c : MME.ReleasedInterior.Split 10) : ℤ :=
  ([2, 4, 4, 2] : List ℤ).getD
    ((seed 1 10).splits.idxOf (sourceShape 1 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 10) : ℚ :=
  ([(-477291395037 / 500000000000), (-431904916687 / 200000000000), (-2166220923849 / 1000000000000), (-954414822653 / 1000000000000)] : List ℚ).getD
    ((seed 1 10).splits.idxOf (sourceShape 1 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 10) : ℚ :=
  ([(-954582790073 / 1000000000000), (-1079762291717 / 500000000000), (-270777615481 / 125000000000), (-238603705663 / 250000000000)] : List ℚ).getD
    ((seed 1 10).splits.idxOf (sourceShape 1 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 10) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 10 =>
        (splitWeight 1 10 1 c : ℝ) / 1000000000000) ≤
          (1 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 10, ∏ i, weights i (c.val i) ≤ 1 := by
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
