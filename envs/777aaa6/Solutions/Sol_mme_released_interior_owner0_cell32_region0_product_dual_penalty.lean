-- Prove2me | solution 1 for mme_released_interior_owner0_cell32_region0_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T12:44:04.529796+00:00
-- url     : https://prove2.me/submissions/b21f6a8f-2d49-4a35-b453-6159dbcee95e

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 32) : ℚ :=
  (splitWeight 0 32 0 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(7787526531600000000000000000000000 / 3939940843633310330028573307876893143), (469807096657200000000000000000000000 / 3939940843633310330028573307876893143), (3312787637735400000000000000000000000 / 3939940843633310330028573307876893143), (469862594062400000000000000000000000 / 3939940843633310330028573307876893143), (7787573957200000000000000000000000 / 3939940843633310330028573307876893143)], ![(407476917681 / 1000000000000), (831232750523 / 1000000000000), (407524725867 / 1000000000000), (1 / 1), (1 / 1)], ![(208675391677 / 500000000000), (396032707331 / 500000000000), (417399986351 / 1000000000000), (1 / 1), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![9, 4, 1, 4, 9], ![2, 1, 2, 0, 0], ![2, 1, 2, 0, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-6226397696819 / 1000000000000), (-132912425629 / 62500000000), (-43343921829 / 250000000000), (-531620172243 / 250000000000), (-6226391606893 / 1000000000000)], ![(-448885495817 / 500000000000), (-92422719239 / 500000000000), (-3506459653 / 3906250000), (0 / 1), (0 / 1)], ![(-218457050929 / 250000000000), (-233111296309 / 1000000000000), (-10921378963 / 12500000000), (0 / 1), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-3113198848409 / 500000000000), (-2126598810063 / 1000000000000), (-34675137463 / 200000000000), (-2126480688971 / 1000000000000), (-1556597901723 / 250000000000)], ![(-897770991633 / 1000000000000), (-184845438477 / 1000000000000), (-897653671167 / 1000000000000), (0 / 1), (0 / 1)], ![(-174765640743 / 200000000000), (-58277824077 / 250000000000), (-873710317039 / 1000000000000), (0 / 1), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 32) : ℤ :=
  ([12, 5, 5, 3, 1, 3, 5, 5, 12] : List ℤ).getD
    ((seed 0 32).splits.idxOf (sourceShape 0 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 32) : ℚ :=
  ([(-7997761684717 / 1000000000000), (-79628864097 / 25000000000), (-3257363779391 / 1000000000000), (-486214249121 / 250000000000), (-591332422099 / 1000000000000), (-388971512341 / 200000000000), (-3257362975073 / 1000000000000), (-1592577166439 / 500000000000), (-1999497700729 / 250000000000)] : List ℚ).getD
    ((seed 0 32).splits.idxOf (sourceShape 0 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 32) : ℚ :=
  ([(-1999440421179 / 250000000000), (-3185154563879 / 1000000000000), (-325736377939 / 100000000000), (-1944856996483 / 1000000000000), (-295666211049 / 500000000000), (-243107195213 / 125000000000), (-101792592971 / 31250000000), (-3185154332877 / 1000000000000), (-1599598160583 / 200000000000)] : List ℚ).getD
    ((seed 0 32).splits.idxOf (sourceShape 0 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 32) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 32 =>
        (splitWeight 0 32 0 c : ℝ) / 1000000000000) ≤
          (1 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 32, ∏ i, weights i (c.val i) ≤ 1 := by
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
