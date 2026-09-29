-- Prove2me | solution 1 for mme_released_interior_owner2_cell36_region0_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T15:54:08.599164+00:00
-- url     : https://prove2.me/submissions/17920ca9-8e21-49b1-a8b2-d9e8c3696d80

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 36) : ℚ :=
  (splitWeight 2 36 0 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(1 / 1), (157568981127 / 1000000000000), (3805700342583 / 1000000000000), (3805673629107 / 1000000000000), (157568760329 / 1000000000000)], ![(66629457992000000000000000000000000 / 839934690402653467933351703125149473), (66629006833000000000000000000000000 / 839934690402653467933351703125149473), (1 / 1), (1 / 1), (1 / 1)], ![(36653289407 / 62500000000), (261372210661 / 250000000000), (586444719179 / 1000000000000), (1 / 1), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![0, 3, -1, -1, 3], ![4, 4, 0, 0, 0], ![1, 0, 1, 0, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(0 / 1), (-1847891941191 / 1000000000000), (668250016437 / 500000000000), (1336493013517 / 1000000000000), (-184789334247 / 100000000000)], ![(-2534177347347 / 1000000000000), (-1267092059267 / 500000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-533663380541 / 1000000000000), (1112114201 / 25000000000), (-533676870781 / 1000000000000), (0 / 1), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(0 / 1), (-184789194119 / 100000000000), (10692000263 / 8000000000), (668246506759 / 500000000000), (-1847893342469 / 1000000000000)], ![(-1267088673673 / 500000000000), (-2534184118533 / 1000000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-26683169027 / 50000000000), (44484568041 / 1000000000000), (-26683843539 / 50000000000), (0 / 1), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 36) : ℤ :=
  ([3, 2, 8, 8, 2, 3] : List ℤ).getD
    ((seed 2 36).splits.idxOf (sourceShape 2 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 36) : ℚ :=
  ([(-1731354185251 / 1000000000000), (-115319976579 / 100000000000), (-1228933517601 / 250000000000), (-983150586113 / 200000000000), (-57659975881 / 50000000000), (-865677242777 / 500000000000)] : List ℚ).getD
    ((seed 2 36).splits.idxOf (sourceShape 2 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 36) : ℚ :=
  ([(-6925416741 / 4000000000), (-1153199765789 / 1000000000000), (-4915734070403 / 1000000000000), (-1228938232641 / 250000000000), (-1153199517619 / 1000000000000), (-1731354485553 / 1000000000000)] : List ℚ).getD
    ((seed 2 36).splits.idxOf (sourceShape 2 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 36) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 36 =>
        (splitWeight 2 36 0 c : ℝ) / 1000000000000) ≤
          (1 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 36, ∏ i, weights i (c.val i) ≤ 1 := by
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
