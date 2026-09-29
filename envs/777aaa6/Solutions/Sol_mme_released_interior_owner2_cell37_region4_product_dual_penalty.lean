-- Prove2me | solution 1 for mme_released_interior_owner2_cell37_region4_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T15:59:44.756707+00:00
-- url     : https://prove2.me/submissions/b4bf4419-fa43-4b81-85d1-b4afa903bf86

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 37) : ℚ :=
  (splitWeight 2 37 4 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(1 / 1), (78971095359 / 500000000000), (3800143889729 / 1000000000000), (237508886213 / 62500000000), (157941782169 / 1000000000000)], ![(587217223408000000000000000000000000 / 7545310567992523147439529284131912359), (1044780985928000000000000000000000000 / 7545310567992523147439529284131912359), (587216671927000000000000000000000000 / 7545310567992523147439529284131912359), (1 / 1), (1 / 1)], ![(599350727163 / 1000000000000), (599350442441 / 1000000000000), (1 / 1), (1 / 1), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![0, 3, -1, -1, 3], ![4, 3, 4, 0, 0], ![1, 1, 0, 0, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(0 / 1), (-922763097219 / 500000000000), (1335038931733 / 1000000000000), (667519240833 / 500000000000), (-1845528781141 / 1000000000000)], ![(-2553286724161 / 1000000000000), (-1977118972859 / 1000000000000), (-510657532661 / 200000000000), (0 / 1), (0 / 1)], ![(-255954165539 / 500000000000), (-31994300383 / 62500000000), (0 / 1), (0 / 1), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(0 / 1), (-1845526194437 / 1000000000000), (667519465867 / 500000000000), (1335038481667 / 1000000000000), (-92276439057 / 50000000000)], ![(-7979021013 / 3125000000), (-988559486429 / 500000000000), (-319160957913 / 125000000000), (0 / 1), (0 / 1)], ![(-511908331077 / 1000000000000), (-511908806127 / 1000000000000), (0 / 1), (0 / 1), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 37) : ℤ :=
  ([3, 8, 2, 2, 8, 3] : List ℤ).getD
    ((seed 2 37).splits.idxOf (sourceShape 2 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 37) : ℚ :=
  ([(-1730157048621 / 1000000000000), (-4910723836381 / 1000000000000), (-1153988847253 / 1000000000000), (-1153988822273 / 1000000000000), (-122768066597 / 25000000000), (-865078531323 / 500000000000)] : List ℚ).getD
    ((seed 2 37).splits.idxOf (sourceShape 2 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 37) : ℚ :=
  ([(-86507852431 / 50000000000), (-245536191819 / 50000000000), (-288497211813 / 250000000000), (-4507768837 / 3906250000), (-4910722663879 / 1000000000000), (-346031412529 / 200000000000)] : List ℚ).getD
    ((seed 2 37).splits.idxOf (sourceShape 2 c)) 0

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
        (splitWeight 2 37 4 c : ℝ) / 1000000000000) ≤
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
