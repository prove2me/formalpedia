-- Prove2me | solution 1 for mme_released_interior_owner2_cell22_region2_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T15:39:19.709739+00:00
-- url     : https://prove2.me/submissions/4860a21f-bae9-4354-ae05-8bfd6b26b79b

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 22) : ℚ :=
  (splitWeight 2 22 2 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(580916349147 / 1000000000000), (26364897271 / 25000000000), (290456614681 / 500000000000), (1 / 1), (1 / 1)], ![(1 / 1), (154871530216000000000000000000000000 / 7638397949276493317652646720193455097), (550256466700000000000000000000000000 / 1091199707039499045378949531456207871), (550254884276000000000000000000000000 / 1091199707039499045378949531456207871), (154871344157000000000000000000000000 / 7638397949276493317652646720193455097)], ![(597720949007 / 1000000000000), (74714923563 / 125000000000), (1 / 1), (1 / 1), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![1, 0, 1, 0, 0], ![0, 6, 1, 1, 6], ![1, 1, 0, 0, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-135787127467 / 250000000000), (5315765169 / 100000000000), (-543153880337 / 1000000000000), (0 / 1), (0 / 1)], ![(0 / 1), (-1949173615871 / 500000000000), (-342324272991 / 500000000000), (-34232571089 / 50000000000), (-3898348433119 / 1000000000000)], ![(-514631274399 / 1000000000000), (-257316942579 / 500000000000), (0 / 1), (0 / 1), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-543148509867 / 1000000000000), (53157651691 / 1000000000000), (-33947117521 / 62500000000), (0 / 1), (0 / 1)], ![(0 / 1), (-3898347231741 / 1000000000000), (-684648545981 / 1000000000000), (-684651421779 / 1000000000000), (-1949174216559 / 500000000000)], ![(-257315637199 / 500000000000), (-514633885157 / 1000000000000), (0 / 1), (0 / 1), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 22) : ℤ :=
  ([8, 2, 3, 3, 2, 8] : List ℤ).getD
    ((seed 2 22).splits.idxOf (sourceShape 2 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 22) : ℚ :=
  ([(-2478067498619 / 500000000000), (-286531194861 / 250000000000), (-1742433700721 / 1000000000000), (-1742433816807 / 1000000000000), (-1146125044489 / 1000000000000), (-1239032054343 / 250000000000)] : List ℚ).getD
    ((seed 2 22).splits.idxOf (sourceShape 2 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 22) : ℚ :=
  ([(-4956134997237 / 1000000000000), (-1146124779443 / 1000000000000), (-21780421259 / 12500000000), (-871216908403 / 500000000000), (-143265630561 / 125000000000), (-4956128217371 / 1000000000000)] : List ℚ).getD
    ((seed 2 22).splits.idxOf (sourceShape 2 c)) 0

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
        (splitWeight 2 22 2 c : ℝ) / 1000000000000) ≤
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
