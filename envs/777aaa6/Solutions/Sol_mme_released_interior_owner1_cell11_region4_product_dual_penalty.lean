-- Prove2me | solution 1 for mme_released_interior_owner1_cell11_region4_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T12:44:29.166337+00:00
-- url     : https://prove2.me/submissions/13a6ce89-b359-4417-a39b-1da5b89c9bb2

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 11) : ℚ :=
  (splitWeight 1 11 4 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(592477914767000000000000000000000000 / 7743823438854703352106257412319591539), (592478731084000000000000000000000000 / 7743823438854703352106257412319591539), (1 / 1), (1 / 1), (1 / 1)], ![(573532814557 / 1000000000000), (266802235441 / 250000000000), (573534450191 / 1000000000000), (1 / 1), (1 / 1)], ![(1 / 1), (150708676809 / 1000000000000), (3930336145937 / 1000000000000), (982585504257 / 250000000000), (75354400853 / 500000000000)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![4, 4, 0, 0, 0], ![1, 0, 1, 0, 0], ![0, 3, -1, -1, 3]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-2570337231303 / 1000000000000), (-1285167926751 / 500000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-555940125991 / 1000000000000), (32523387429 / 500000000000), (-555937274137 / 1000000000000), (0 / 1), (0 / 1)], ![(0 / 1), (-946203299153 / 500000000000), (68436247777 / 50000000000), (85545403083 / 62500000000), (-75696230783 / 40000000000)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-1285168615651 / 500000000000), (-2570335853501 / 1000000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-55594012599 / 100000000000), (65046774859 / 1000000000000), (-69492159267 / 125000000000), (0 / 1), (0 / 1)], ![(0 / 1), (-378481319661 / 200000000000), (1368724955541 / 1000000000000), (1368726449329 / 1000000000000), (-946202884787 / 500000000000)]]

private def alphaScale (c : MME.ReleasedInterior.Split 11) : ℤ :=
  ([3, 2, 8, 8, 2, 3] : List ℤ).getD
    ((seed 1 11).splits.idxOf (sourceShape 1 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 11) : ℚ :=
  ([(-1757549549897 / 1000000000000), (-1136564007113 / 1000000000000), (-1003736625381 / 200000000000), (-2509339863 / 500000000), (-35517628847 / 31250000000), (-878774765083 / 500000000000)] : List ℚ).getD
    ((seed 1 11).splits.idxOf (sourceShape 1 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 11) : ℚ :=
  ([(-219693693737 / 125000000000), (-142070500889 / 125000000000), (-627335390863 / 125000000000), (-5018679725999 / 1000000000000), (-1136564123103 / 1000000000000), (-351509906033 / 200000000000)] : List ℚ).getD
    ((seed 1 11).splits.idxOf (sourceShape 1 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 11) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 11 =>
        (splitWeight 1 11 4 c : ℝ) / 1000000000000) ≤
          (1 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 11, ∏ i, weights i (c.val i) ≤ 1 := by
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
