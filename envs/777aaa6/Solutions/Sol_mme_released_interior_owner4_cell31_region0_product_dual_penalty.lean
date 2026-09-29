-- Prove2me | solution 1 for mme_released_interior_owner4_cell31_region0_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-24T09:19:02.28791+00:00
-- url     : https://prove2.me/submissions/3084a947-91c2-41e2-8971-139357dec879

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 31) : ℚ :=
  (splitWeight 4 31 0 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(13353533453 / 250000000000), (2066607140231 / 1000000000000), (6385209834957 / 500000000000), (129162888487 / 62500000000), (26707069293 / 500000000000)], ![(49334656007500000000000000000000000 / 2181139811515842090290309577427888387), (49334632364500000000000000000000000 / 2181139811515842090290309577427888387), (1 / 1), (1 / 1), (1 / 1)], ![(135994824521 / 500000000000), (1451028018511 / 1000000000000), (362756793623 / 250000000000), (33998820041 / 125000000000), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![5, -1, -3, -1, 5], ![6, 6, 0, 0, 0], ![2, 0, 0, 2, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-292967988991 / 100000000000), (362954099927 / 500000000000), (63678288331 / 25000000000), (725907752531 / 1000000000000), (-2929679800533 / 1000000000000)], ![(-757795214553 / 200000000000), (-3788976552003 / 1000000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-1301991268403 / 1000000000000), (372272283509 / 1000000000000), (372271701839 / 1000000000000), (-260397583593 / 200000000000), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-2929679889909 / 1000000000000), (145181639971 / 200000000000), (2547131533241 / 1000000000000), (181476938133 / 250000000000), (-732419950133 / 250000000000)], ![(-947244018191 / 250000000000), (-1894488276001 / 500000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-650995634201 / 500000000000), (37227228351 / 100000000000), (4653396273 / 12500000000), (-325496979491 / 250000000000), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 31) : ℤ :=
  ([12, 4, 2, 7, 7, 2, 4, 12] : List ℤ).getD
    ((seed 4 31).splits.idxOf (sourceShape 4 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 31) : ℚ :=
  ([(-250645223131 / 31250000000), (-33634950459 / 12500000000), (-217393209421 / 250000000000), (-4365055790899 / 1000000000000), (-873012013573 / 200000000000), (-173914547051 / 200000000000), (-2690796650311 / 1000000000000), (-200516108969 / 25000000000)] : List ℚ).getD
    ((seed 4 31).splits.idxOf (sourceShape 4 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 31) : ℚ :=
  ([(-8020647140191 / 1000000000000), (-2690796036719 / 1000000000000), (-869572837683 / 1000000000000), (-2182527895449 / 500000000000), (-545632508483 / 125000000000), (-434786367627 / 500000000000), (-269079665031 / 100000000000), (-8020644358759 / 1000000000000)] : List ℚ).getD
    ((seed 4 31).splits.idxOf (sourceShape 4 c)) 0

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
        (splitWeight 4 31 0 c : ℝ) / 1000000000000) ≤
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
