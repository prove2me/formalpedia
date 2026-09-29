-- Prove2me | solution 1 for mme_released_interior_owner0_cell22_region3_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T12:37:21.217371+00:00
-- url     : https://prove2.me/submissions/f0c4f693-ab34-4e8b-b6a7-f2166e56bfaf

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 22) : ℚ :=
  (splitWeight 0 22 3 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(23320434367440000000000000000000000 / 304275121340222602907133909154982717), (42047914317800000000000000000000000 / 304275121340222602907133909154982717), (23320835748760000000000000000000000 / 304275121340222602907133909154982717), (1 / 1), (1 / 1)], ![(1 / 1), (155931267279 / 1000000000000), (1916813520447 / 500000000000), (3833662549871 / 1000000000000), (155931447761 / 1000000000000)], ![(299204033791 / 500000000000), (598412450303 / 1000000000000), (1 / 1), (1 / 1), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![4, 3, 4, 0, 0], ![0, 3, -1, -1, 3], ![1, 1, 0, 0, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-1284301154423 / 500000000000), (-1979122511409 / 1000000000000), (-2568585097423 / 1000000000000), (0 / 1), (0 / 1)], ![(0 / 1), (-1858339963189 / 1000000000000), (1343811363129 / 1000000000000), (335955156397 / 250000000000), (-116146175359 / 62500000000)], ![(-513482370491 / 1000000000000), (-513475046551 / 1000000000000), (0 / 1), (0 / 1), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-513720461769 / 200000000000), (-123695156963 / 62500000000), (-1284292548711 / 500000000000), (0 / 1), (0 / 1)], ![(0 / 1), (-464584990797 / 250000000000), (134381136313 / 100000000000), (1343820625589 / 1000000000000), (-1858338805743 / 1000000000000)], ![(-51348237049 / 100000000000), (-10269500931 / 20000000000), (0 / 1), (0 / 1), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 22) : ℤ :=
  ([3, 8, 2, 2, 8, 3] : List ℤ).getD
    ((seed 0 22).splits.idxOf (sourceShape 0 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 22) : ℚ :=
  ([(-108641045613 / 62500000000), (-617552935637 / 125000000000), (-1148786194831 / 1000000000000), (-1148784256311 / 1000000000000), (-4940400107143 / 1000000000000), (-108641006549 / 62500000000)] : List ℚ).getD
    ((seed 0 22).splits.idxOf (sourceShape 0 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 22) : ℚ :=
  ([(-1738256729807 / 1000000000000), (-988084697019 / 200000000000), (-114878619483 / 100000000000), (-114878425631 / 100000000000), (-2470200053571 / 500000000000), (-1738256104783 / 1000000000000)] : List ℚ).getD
    ((seed 0 22).splits.idxOf (sourceShape 0 c)) 0

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
        (splitWeight 0 22 3 c : ℝ) / 1000000000000) ≤
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
