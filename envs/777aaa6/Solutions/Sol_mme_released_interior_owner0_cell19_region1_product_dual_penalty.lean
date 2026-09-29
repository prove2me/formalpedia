-- Prove2me | solution 1 for mme_released_interior_owner0_cell19_region1_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T12:25:24.38024+00:00
-- url     : https://prove2.me/submissions/b77604e0-56c3-4026-ad48-1b769c02b073

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 19) : ℚ :=
  (splitWeight 0 19 1 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(66824044410000000000000000000000000 / 3392825789163510027895024503920711167), (415601702330500000000000000000000000 / 10178477367490530083685073511762133501), (200472502090000000000000000000000000 / 10178477367490530083685073511762133501), (1 / 1), (1 / 1)], ![(103877918721 / 250000000000), (772787962797 / 1000000000000), (16620497709 / 40000000000), (1 / 1), (1 / 1)], ![(38934261999 / 1000000000000), (1114611332391 / 500000000000), (2232448170433 / 125000000000), (2229226846181 / 1000000000000), (486678281 / 12500000000)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![6, 5, 6, 0, 0], ![2, 1, 2, 0, 0], ![5, -1, -4, -1, 5]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-1963677728621 / 500000000000), (-3198303352649 / 1000000000000), (-3927353617287 / 1000000000000), (0 / 1), (0 / 1)], ![(-175648913337 / 200000000000), (-32218821537 / 125000000000), (-439121359373 / 500000000000), (0 / 1), (0 / 1)], ![(-3245880644827 / 1000000000000), (50103308993 / 62500000000), (2882540359247 / 1000000000000), (801654819607 / 1000000000000), (-3245880632473 / 1000000000000)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-3927355457241 / 1000000000000), (-399787919081 / 125000000000), (-1963676808643 / 500000000000), (0 / 1), (0 / 1)], ![(-219561141671 / 250000000000), (-51550114459 / 200000000000), (-175648543749 / 200000000000), (0 / 1), (0 / 1)], ![(-1622940322413 / 500000000000), (801652943889 / 1000000000000), (180158772453 / 62500000000), (100206852451 / 125000000000), (-405735079059 / 125000000000)]]

private def alphaScale (c : MME.ReleasedInterior.Split 19) : ℤ :=
  ([12, 5, 3, 5, 1, 5, 3, 5, 12] : List ℤ).getD
    ((seed 0 19).splits.idxOf (sourceShape 0 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 19) : ℚ :=
  ([(-4025740327879 / 500000000000), (-3383451259849 / 1000000000000), (-480764451287 / 250000000000), (-3274893054939 / 1000000000000), (-573513565699 / 1000000000000), (-3274893172281 / 1000000000000), (-1923057836313 / 1000000000000), (-26433212467 / 7812500000), (-4025738490327 / 500000000000)] : List ℚ).getD
    ((seed 0 19).splits.idxOf (sourceShape 0 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 19) : ℚ :=
  ([(-8051480655757 / 1000000000000), (-422931407481 / 125000000000), (-1923057805147 / 1000000000000), (-1637446527469 / 500000000000), (-286756782849 / 500000000000), (-81872329307 / 25000000000), (-240382229539 / 125000000000), (-135338047831 / 40000000000), (-2012869245163 / 250000000000)] : List ℚ).getD
    ((seed 0 19).splits.idxOf (sourceShape 0 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 19) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 19 =>
        (splitWeight 0 19 1 c : ℝ) / 1000000000000) ≤
          (1 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 19, ∏ i, weights i (c.val i) ≤ 1 := by
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
