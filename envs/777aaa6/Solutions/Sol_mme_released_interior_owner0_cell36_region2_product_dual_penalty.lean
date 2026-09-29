-- Prove2me | solution 1 for mme_released_interior_owner0_cell36_region2_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T12:44:11.820356+00:00
-- url     : https://prove2.me/submissions/31946938-78dc-47da-aeb2-c0a198d694a0

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 36) : ℚ :=
  (splitWeight 0 36 2 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(1 / 1), (39383724246750000000000000000000000 / 1890006289142897183758591898501489521), (951593994936750000000000000000000000 / 1890006289142897183758591898501489521), (951594686201750000000000000000000000 / 1890006289142897183758591898501489521), (39383720114000000000000000000000000 / 1890006289142897183758591898501489521)], ![(74955152249 / 125000000000), (59964168227 / 100000000000), (1 / 1), (1 / 1), (1 / 1)], ![(586453140887 / 1000000000000), (1045386843953 / 1000000000000), (293227174301 / 500000000000), (1 / 1), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![0, 6, 1, 1, 6], ![1, 1, 0, 0, 0], ![1, 0, 1, 0, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(0 / 1), (-3870982794863 / 1000000000000), (-17154924193 / 25000000000), (-686196241291 / 1000000000000), (-1935491449899 / 500000000000)], ![(-102284754527 / 200000000000), (-63927874797 / 125000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-533662510267 / 1000000000000), (8877400503 / 200000000000), (-266830225457 / 500000000000), (0 / 1), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(0 / 1), (-1935491397431 / 500000000000), (-686196967719 / 1000000000000), (-68619624129 / 100000000000), (-3870982899797 / 1000000000000)], ![(-255711886317 / 500000000000), (-4091383987 / 8000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-266831255133 / 500000000000), (11096750629 / 250000000000), (-533660450913 / 1000000000000), (0 / 1), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 36) : ℤ :=
  ([8, 3, 2, 2, 3, 8] : List ℤ).getD
    ((seed 0 36).splits.idxOf (sourceShape 0 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 36) : ℚ :=
  ([(-4916066244089 / 1000000000000), (-865640595633 / 500000000000), (-57661648179 / 50000000000), (-1153233011411 / 1000000000000), (-1731281749933 / 1000000000000), (-196642767309 / 40000000000)] : List ℚ).getD
    ((seed 0 36).splits.idxOf (sourceShape 0 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 36) : ℚ :=
  ([(-614508280511 / 125000000000), (-346256238253 / 200000000000), (-1153232963579 / 1000000000000), (-115323301141 / 100000000000), (-432820437483 / 250000000000), (-1229017295681 / 250000000000)] : List ℚ).getD
    ((seed 0 36).splits.idxOf (sourceShape 0 c)) 0

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
        (splitWeight 0 36 2 c : ℝ) / 1000000000000) ≤
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
