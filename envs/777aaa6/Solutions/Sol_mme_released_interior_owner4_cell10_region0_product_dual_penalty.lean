-- Prove2me | solution 1 for mme_released_interior_owner4_cell10_region0_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-24T09:15:39.915279+00:00
-- url     : https://prove2.me/submissions/84fdf701-1032-4d44-a57b-a12c31436ae2

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 10) : ℚ :=
  (splitWeight 4 10 0 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(850503400441 / 1000000000000), (850760223527 / 1000000000000), (1 / 1), (1 / 1), (1 / 1)], ![(169629633745400000000000000000000000 / 755329067631037773115331898836786207), (169712092017400000000000000000000000 / 755329067631037773115331898836786207), (1 / 1), (1 / 1), (1 / 1)], ![(1 / 1), (1 / 1), (597569807501 / 1000000000000), (2016720267053 / 1000000000000), (301216198857 / 500000000000)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![1, 1, 0, 0, 0], ![3, 3, 0, 0, 0], ![0, 0, 1, -1, 1]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-40481717247 / 250000000000), (-80812474299 / 500000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-746768035047 / 500000000000), (-1493050080501 / 1000000000000), (0 / 1), (0 / 1), (0 / 1)], ![(0 / 1), (0 / 1), (-128721042341 / 250000000000), (28058902469 / 40000000000), (-506779822877 / 1000000000000)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-161926868987 / 1000000000000), (-161624948597 / 1000000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-1493536070093 / 1000000000000), (-2986100161 / 2000000000), (0 / 1), (0 / 1), (0 / 1)], ![(0 / 1), (0 / 1), (-514884169363 / 1000000000000), (350736280863 / 500000000000), (-126694955719 / 250000000000)]]

private def alphaScale (c : MME.ReleasedInterior.Split 10) : ℤ :=
  ([2, 4, 4, 2] : List ℤ).getD
    ((seed 4 10).splits.idxOf (sourceShape 4 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 10) : ℚ :=
  ([(-476844228483 / 500000000000), (-540560690489 / 250000000000), (-433911839693 / 200000000000), (-953504387763 / 1000000000000)] : List ℚ).getD
    ((seed 4 10).splits.idxOf (sourceShape 4 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 10) : ℚ :=
  ([(-190737691393 / 200000000000), (-432448552391 / 200000000000), (-8474840619 / 3906250000), (-476752193881 / 500000000000)] : List ℚ).getD
    ((seed 4 10).splits.idxOf (sourceShape 4 c)) 0

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
        (splitWeight 4 10 0 c : ℝ) / 1000000000000) ≤
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
