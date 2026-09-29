-- Prove2me | solution 1 for mme_released_interior_owner2_cell12_region1_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T15:15:56.07313+00:00
-- url     : https://prove2.me/submissions/af6d7e8d-a4b0-4941-8468-5b914d065595

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 12) : ℚ :=
  (splitWeight 2 12 1 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(194826076587 / 500000000000), (19482675727 / 50000000000), (1 / 1), (1 / 1), (1 / 1)], ![(142040839878500000000000000000000000 / 8954786372587761902233457187708218401), (685952743489500000000000000000000000 / 8954786372587761902233457187708218401), (685955156027500000000000000000000000 / 8954786372587761902233457187708218401), (142042198194500000000000000000000000 / 8954786372587761902233457187708218401), (1 / 1)], ![(52700455827 / 1000000000000), (122479697669 / 62500000000), (14375062084903 / 1000000000000), (1959688733307 / 1000000000000), (52700477287 / 1000000000000)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![2, 2, 0, 0, 0], ![6, 4, 4, 6, 0], ![5, 0, -3, 0, 5]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-94250085279 / 100000000000), (-471248679499 / 500000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-1035957209381 / 250000000000), (-1284567360121 / 500000000000), (-1284565601593 / 500000000000), (-828763854943 / 200000000000), (0 / 1)], ![(-735782793501 / 250000000000), (42048670387 / 62500000000), (2665494905623 / 1000000000000), (672785651093 / 1000000000000), (-2943130766797 / 1000000000000)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-942500852789 / 1000000000000), (-942497358997 / 1000000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-4143828837523 / 1000000000000), (-2569134720241 / 1000000000000), (-513826240637 / 200000000000), (-2071909637357 / 500000000000), (0 / 1)], ![(-2943131174003 / 1000000000000), (672778726193 / 1000000000000), (333186863203 / 125000000000), (336392825547 / 500000000000), (-735782691699 / 250000000000)]]

private def alphaScale (c : MME.ReleasedInterior.Split 12) : ℤ :=
  ([12, 7, 5, 2, 2, 5, 7, 12] : List ℤ).getD
    ((seed 2 12).splits.idxOf (sourceShape 2 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 12) : ℚ :=
  ([(-8029460455683 / 1000000000000), (-2206770272731 / 500000000000), (-1419424960971 / 500000000000), (-169227434723 / 200000000000), (-846137150353 / 1000000000000), (-709712459 / 250000000), (-1103385350323 / 250000000000), (-4014723903507 / 500000000000)] : List ℚ).getD
    ((seed 2 12).splits.idxOf (sourceShape 2 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 12) : ℚ :=
  ([(-4014730227841 / 500000000000), (-4413540545461 / 1000000000000), (-2838849921941 / 1000000000000), (-423068586807 / 500000000000), (-52883571897 / 62500000000), (-2838849835999 / 1000000000000), (-4413541401291 / 1000000000000), (-8029447807013 / 1000000000000)] : List ℚ).getD
    ((seed 2 12).splits.idxOf (sourceShape 2 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 12) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 12 =>
        (splitWeight 2 12 1 c : ℝ) / 1000000000000) ≤
          (1 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 12, ∏ i, weights i (c.val i) ≤ 1 := by
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
