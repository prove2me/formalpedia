-- Prove2me | solution 1 for mme_released_interior_owner5_cell31_region0_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-24T09:23:32.962984+00:00
-- url     : https://prove2.me/submissions/bb68382c-6f2d-4238-9f5f-2274b503d1a6

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 31) : ℚ :=
  (splitWeight 5 31 0 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(2669896021 / 50000000000), (516501223877 / 250000000000), (3193656109899 / 250000000000), (1033005358319 / 500000000000), (10679584099 / 200000000000)], ![(39450059399 / 100000000000), (24656325067 / 62500000000), (1 / 1), (1 / 1), (1 / 1)], ![(135744415397500000000000000000000000 / 8734018816856122607431018523656033779), (242172989177000000000000000000000000 / 2911339605618707535810339507885344593), (726520120584500000000000000000000000 / 8734018816856122607431018523656033779), (135744690917500000000000000000000000 / 8734018816856122607431018523656033779), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![5, -1, -3, -1, 5], ![2, 2, 0, 0, 0], ![7, 4, 4, 7, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-146499173861 / 50000000000), (725616740253 / 1000000000000), (1273730368791 / 500000000000), (725619557827 / 1000000000000), (-366247934477 / 125000000000)], ![(-46506731651 / 50000000000), (-930133094159 / 1000000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-416420706939 / 100000000000), (-2486716297717 / 1000000000000), (-77709834707 / 31250000000), (-832841007939 / 200000000000), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-2929983477219 / 1000000000000), (362808370127 / 500000000000), (2547460737583 / 1000000000000), (181404889457 / 250000000000), (-585996695163 / 200000000000)], ![(-930134633019 / 1000000000000), (-465066547079 / 500000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-4164207069389 / 1000000000000), (-621679074429 / 250000000000), (-2486714710623 / 1000000000000), (-2082102519847 / 500000000000), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 31) : ℤ :=
  ([12, 7, 4, 2, 2, 4, 7, 12] : List ℤ).getD
    ((seed 5 31).splits.idxOf (sourceShape 5 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 31) : ℚ :=
  ([(-8024325177699 / 1000000000000), (-4368720605747 / 1000000000000), (-2691231372911 / 1000000000000), (-869388654291 / 1000000000000), (-434694303031 / 500000000000), (-1345615532261 / 500000000000), (-4368722932503 / 1000000000000), (-8024321610213 / 1000000000000)] : List ℚ).getD
    ((seed 5 31).splits.idxOf (sourceShape 5 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 31) : ℚ :=
  ([(-8024325177697 / 1000000000000), (-2184360302873 / 500000000000), (-269123137291 / 100000000000), (-86938865429 / 100000000000), (-869388606061 / 1000000000000), (-2691231064521 / 1000000000000), (-4368722932501 / 1000000000000), (-2006080402553 / 250000000000)] : List ℚ).getD
    ((seed 5 31).splits.idxOf (sourceShape 5 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 31) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 31 =>
        (splitWeight 5 31 0 c : ℝ) / 1000000000000) ≤
          (1 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 31, ∏ i, weights i (c.val i) ≤ 1 := by
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
